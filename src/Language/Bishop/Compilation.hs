module Language.Bishop.Compilation where

import           Language.Bishop.Term
import           Language.Bishop.Net
import           Data.Word
import           Data.Vector.Unboxed         (Vector)
import qualified Data.Vector.Unboxed         as V
import           Data.Vector.Unboxed.Mutable (MVector, write)
import qualified Data.Vector.Unboxed.Mutable as MV
import           Control.Monad.ST

mkLoop i   = mkInit i (L, i)
mkWire i j = mkInit i (L, j)

shiftNodes :: Word64 -> Vector Node -> Vector Node
shiftNodes s nodes = V.map (\(i,m,l,r) -> (i,m+s,l+s,r+s)) nodes

lastFreeNode :: Vector Node -> Int
lastFreeNode nodes = go nodes (V.length nodes - 1) where
  go :: Vector Node -> Int -> Int
  go nodes n =
    case _kind $ getInfo (nodes V.! n) of
      Init -> n
      _    -> if n == 0 then error "This should not happen" else go nodes (n - 1)

writeSlot :: MVector s Node -> Int -> Slot -> (Slot, Word64) -> ST s ()
writeSlot mv idx x p = do
  node <- MV.read mv idx
  write mv idx $ setSlot node x p

changeKind :: MVector s Node -> Int -> Kind -> ST s ()
changeKind mv idx kind = do
  (i,m,l,r) <- MV.read mv idx
  write mv idx (infoBits ((readInfoBits i) {_kind = kind}),m,l,r)

linkWire :: MVector s Node -> Word64 -> (Slot, Word64) -> ST s ()
linkWire mv wirePos (portSlot, portPos) = do
  (s,i) <- getPort L <$> MV.read mv (fromEnum wirePos)
  writeSlot mv (fromEnum i) s (portSlot, portPos)
  (s,i) <- getPort L <$> MV.read mv (fromEnum wirePos) -- Need to fetch again in case it was a loop
  writeSlot mv (fromEnum portPos) portSlot  (s,i)

compile :: Anon -> Net
compile trm = Net nodes [] (findRedexes nodes)
  where
    nodes :: Vector Node
    nodes =  go 0 trm
    go :: Int -> Anon -> Vector Node
    go dep trm = case trm of
      VarA 0       ->
        if dep < 1
        then error "Term has free variables"
        else V.constructN (dep + 1) build
        where
          build :: Vector Node -> Node
          build as
            | V.length as == 0   = mkWire 0 (toEnum dep)
            | V.length as == dep = mkWire (toEnum dep) 0
            | otherwise          = mkLoop (toEnum $ V.length as)
      VarA idx     ->
        let
          net   = go (dep - 1) $ VarA (idx - 1)
          len   = toEnum $ V.length net
          (s,i) = getPort L $ net V.! 0
          scop  = mkScop len (s,i) (L,0) 0 -- TODO: correct level. Is it really necessary?
          loop  = mkLoop $ len + 1

          update :: MVector s Node -> ST s ()
          update mv = do
            writeSlot mv 0            L (L, len)
            writeSlot mv (fromEnum i) s (M, len)
        in 
          V.modify update net V.++ V.fromList [scop, loop]
      LamA bdy     ->
        let
          net = go (dep + 1) bdy
          pos = lastFreeNode net

          update :: MVector s Node -> ST s ()
          update mv = do
            changeKind mv pos Abst 
            linkWire mv 0 (R, toEnum pos)
            writeSlot mv 0            L (M, toEnum pos)
            writeSlot mv pos          M (L, 0)
        in
          V.modify update net

      AppA fun arg ->
        let
          net1 = go dep fun
          len  = toEnum $ V.length net1
          net  = net1 V.++ (shiftNodes len $ go dep arg)

          nextWire :: MVector s Node -> Int -> ST s Int
          nextWire mv a = do
            kind <- _kind <$> getInfo <$> MV.read mv (a + 1)
            case kind of
              Init -> return (a + 1)
              _    -> nextWire mv (a + 1)
          pairUp :: MVector s Node -> (Int, Int) -> Int -> ST s ()
          pairUp mv (a0, b0) n =
            if n < 1
            then return ()
            else do
              a1 <- nextWire mv a0
              b1 <- nextWire mv b0
              changeKind mv a1 Dupl 
              linkWire mv (toEnum b1) (R, toEnum a1)
              writeSlot mv b1 L (M, toEnum a1)
              writeSlot mv a1 M (L, toEnum b1)
              pairUp mv (a1,b1) (n-1)
          update :: MVector s Node -> ST s ()
          update mv = do
            linkWire mv len (R, len)
            changeKind mv (fromEnum len) Appl -- reuses the space freed by the wire, now main and left ports should be populated
            linkWire mv 0 (M, len)
            writeSlot mv 0              L  (L, len)
            writeSlot mv (fromEnum len) L  (L, 0)
            pairUp mv (0, fromEnum len) dep
        in
          V.modify update net
      RefA cid     -> error "Reference compilation TODO"

twoAnon :: Anon
twoAnon = LamA (LamA (AppA (VarA 1) (AppA (VarA 1) (VarA 0))))

testCompile :: Net
testCompile = compile twoAnon
