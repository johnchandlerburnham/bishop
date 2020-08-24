module Language.Bishop.Compilation where

import           Language.Bishop.Term
import           Language.Bishop.Net
import           Data.Word
import           Data.Vector.Unboxed         (Vector)
import qualified Data.Vector.Unboxed         as V
import           Data.Vector.Unboxed.Mutable (MVector)
import qualified Data.Vector.Unboxed.Mutable as MV
import           Control.Monad
import           Control.Monad.ST

mkLoop i   = mkInit i (L, i)
mkWire i j = mkInit i (L, j)

isLoop :: Int -> Node -> Bool
isLoop pos (i,_,l,_) = l == toEnum pos && _leftSlot (readInfoBits i) == L

shiftNodes :: Word64 -> MVector s Node -> ST s ()
shiftNodes s nodes = go nodes (MV.length nodes)
  where
    go :: MVector s Node -> Int -> ST s ()
    go nodes 0 = return ()
    go nodes i = do
      MV.modify nodes (\(i,m,l,r) -> (i,m+s,l+s,r+s)) (i-1)
      go nodes (i-1)

catVector :: MV.Unbox a => MVector s a -> MVector s a -> ST s (MVector s a)
catVector xs ys = do
  xs <- MV.grow xs leny
  go xs ys 0
  return xs
    where
      lenx = MV.length xs
      leny = MV.length ys
      go :: MV.Unbox a => MVector s a -> MVector s a -> Int -> ST s ()
      go xs ys pos =
        if pos == leny
        then return ()
        else do
          y <- MV.read ys pos
          MV.write xs (pos + lenx) y
          go xs ys (pos+1)

lastWire :: MVector s Node -> ST s Int
lastWire nodes = go nodes (MV.length nodes - 1) where
  go :: MVector s Node -> Int -> ST s Int
  go nodes n = do
    kind <- _kind <$> getInfo <$> MV.read nodes n
    case kind of
      Init -> return n
      _    -> if n == 0 then error "This should not happen" else go nodes (n - 1)

writeSlot :: MVector s Node -> Int -> Slot -> (Slot, Word64) -> ST s ()
writeSlot mv idx x p = do
  node <- MV.read mv idx
  MV.write mv idx $ setSlot node x p

changeKind :: MVector s Node -> Int -> Kind -> ST s ()
changeKind mv idx kind = do
  (i,m,l,r) <- MV.read mv idx
  MV.write mv idx (infoBits ((readInfoBits i) {_kind = kind}),m,l,r)

releaseNode :: MVector s Node -> Int -> ST s ()
releaseNode mv idx = do
  (i,m,l,r) <- MV.read mv idx
  MV.write mv idx (infoBits ((readInfoBits i) {_isFree = True}),m,l,r)

linkWire :: MVector s Node -> Word64 -> (Slot, Word64) -> ST s ()
linkWire mv wirePos (portSlot, portPos) = do
  (s,i) <- getPort L <$> MV.read mv (fromEnum wirePos)
  writeSlot mv (fromEnum i) s (portSlot, portPos)
  (s,i) <- getPort L <$> MV.read mv (fromEnum wirePos) -- Need to fetch again in case it was a loop
  writeSlot mv (fromEnum portPos) portSlot  (s,i)

findFreeNodes :: V.Vector Node -> [(Word64)]
findFreeNodes vs = V.ifoldr addFreeNode [] vs
  where
    addFreeNode :: Int -> Node -> [Word64] -> [Word64]
    addFreeNode i node fs
      | _isFree (getInfo node) = toEnum i : fs
      | otherwise              = fs

toNet :: Vector Node -> Net
toNet nodes = Net nodes (findFreeNodes nodes) (findRedexes nodes)

compile :: Anon -> Net
compile trm = toNet nodes
  where
    nodes = runST $ do
      mnodes <- go trm 0
      V.freeze mnodes
    go :: Anon -> Int -> ST s (MVector s Node)
    go trm dep = case trm of
      VarA 0       ->
        if dep < 1
        then error "Term has free variables"
        else V.thaw $ V.constructN (dep + 1) build
        where
          build :: Vector Node -> Node
          build as
            | V.length as == 0   = mkWire 0 (toEnum dep)
            | V.length as == dep = mkWire (toEnum dep) 0
            | otherwise          = mkLoop (toEnum $ V.length as)
      VarA idx     -> do
        net <- go (VarA (idx - 1)) (dep - 1)
        let len      = toEnum $ MV.length net
        (s,i)        <- getPort L <$> MV.read net 0
        writeSlot net 0            L (L, len)
        writeSlot net (fromEnum i) s (M, len)
        net <- MV.grow net 2
        let scop     = mkScop len (s,i) (L,0) 0 -- TODO: correct level. Is it really necessary?
        let loop     = mkLoop $ len + 1
        MV.write net (fromEnum len) scop
        MV.write net (fromEnum len + 1) loop
        return net
      LamA bdy     -> do
        net <- go bdy (dep + 1)
        pos          <- lastWire net
        changeKind net pos Abst 
        linkWire  net 0 (R, toEnum pos)
        writeSlot net 0   L (M, toEnum pos)
        writeSlot net pos M (L, 0)
        return net

      AppA fun arg -> do
        net1 <- go fun dep
        let len        = toEnum $ MV.length net1
        net2 <- go arg dep
        shiftNodes len net2
        net            <- catVector net1 net2

        let nextWire :: MVector s Node -> Int -> ST s Int
            nextWire mv a = do
              kind <- _kind <$> getInfo <$> MV.read mv (a + 1)
              case kind of
                Init -> return (a + 1)
                _    -> nextWire mv (a + 1)
        let pairUp :: MVector s Node -> (Int, Int) -> Int -> ST s ()
            pairUp mv (a0, b0) n =
              if n < 1
              then return ()
              else do
                a1 <- nextWire mv a0
                b1 <- nextWire mv b0
                changeKind mv a1 Dupl 
                node1 <- MV.read mv a1
                node2 <- MV.read mv b1
                if isLoop a1 node1 || isLoop b1 node2
                  then do
                  releaseNode mv a1
                  when (isLoop b1 node2) (linkWire mv (toEnum a1) (L, toEnum b1))
                  pairUp mv (a1,b1) (n-1)
                  else do
                  linkWire mv (toEnum b1) (R, toEnum a1)
                  writeSlot mv b1 L (M, toEnum a1)
                  writeSlot mv a1 M (L, toEnum b1)
                  pairUp mv (a1,b1) (n-1)

        linkWire net len (R, len)
        changeKind net (fromEnum len) Appl -- reuses the space freed by the wire, now main and left ports should be populated
        linkWire net 0 (M, len)
        writeSlot net 0              L  (L, len)
        writeSlot net (fromEnum len) L  (L, 0)
        pairUp net (0, fromEnum len) dep
        return net
      RefA cid     -> error "Reference compilation TODO"

churchTwo :: Anon
churchTwo = LamA (LamA (AppA (VarA 1) (AppA (VarA 1) (VarA 0))))

testCompile :: Net
testCompile = compile churchTwo
