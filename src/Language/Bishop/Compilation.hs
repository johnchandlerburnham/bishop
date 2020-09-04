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
import           Data.STRef

doTimes :: Monad m => Int -> (Int -> Bool) -> (Int -> Int) -> (Int -> m a) -> m ()
doTimes i p inc body
  | p i = do
      body i
      doTimes (inc i) p inc body
  | otherwise = return ()

mkLoop i   = mkInit i (L, i)
mkWire i j = mkInit i (L, j)

isLoop :: MVector s Node -> Int -> ST s Bool
isLoop mv pos = do
  (i,_,l,_) <- MV.read mv pos
  return (l == toEnum pos && _leftSlot (readInfoBits i) == L)

shiftNodes :: Word64 -> MVector s Node -> ST s ()
shiftNodes s nodes = doTimes 0 (< MV.length nodes) (+ 1) (\i -> MV.modify nodes (\(i,m,l,r) -> (i,m+s,l+s,r+s)) i)

catVector :: MV.Unbox a => MVector s a -> MVector s a -> ST s (MVector s a)
catVector xs ys = do
  let lenx = MV.length xs
  let leny = MV.length ys
  xs <- MV.grow xs leny
  let body pos = do
        y <- MV.read ys pos
        MV.write xs (pos + lenx) y
  doTimes 0 (< leny) (+ 1) body
  return xs

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
  MV.write mv idx $ substSlot node x p

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
  (s,i) <- portDest L <$> MV.read mv (fromEnum wirePos)
  writeSlot mv (fromEnum i) s (portSlot, portPos)
  (s,i) <- portDest L <$> MV.read mv (fromEnum wirePos) -- Need to fetch again in case it was a loop
  writeSlot mv (fromEnum portPos) portSlot  (s,i)

findFreeNodes :: Vector Node -> [(Word64)]
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
        let len = toEnum $ MV.length net
        (s,i) <- portDest L <$> MV.read net 0
        writeSlot net 0            L (L, len)
        writeSlot net (fromEnum i) s (M, len)
        net   <- MV.grow net 2
        let scop = mkScop len (s,i) (L,0) 0 -- TODO: correct level. Is it really necessary?
        let loop = mkLoop $ len + 1
        MV.write net (fromEnum len) scop
        MV.write net (fromEnum len + 1) loop
        return net
      LamA bdy     -> do
        net <- go bdy (dep + 1)
        pos <- lastWire net
        changeKind net pos Abst
        linkWire  net 0 (R, toEnum pos)
        writeSlot net 0   L (M, toEnum pos)
        writeSlot net pos M (L, 0)
        return net

      AppA fun arg -> do
        net1 <- go fun dep
        let len = toEnum $ MV.length net1
        net2 <- go arg dep
        shiftNodes len net2
        net  <- catVector net1 net2

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
                loopA <- isLoop mv a1
                loopB <- isLoop mv b1
                if loopA || loopB
                  then do
                  releaseNode mv a1
                  when loopB (linkWire mv (toEnum a1) (L, toEnum b1))
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

unwind :: MVector s Node -> ST s ()
unwind nodes = do
  let body pos = do
        (b,iM,iL,iR) <- MV.read nodes pos
        let info = readInfoBits b
        if _kind info == Appl
          then do
          let sM = _mainSlot info
          let sL = _leftSlot info
          let sR = _rigtSlot info
          MV.write nodes pos $ mkAppl pos (sL,iL) (sR,iR) (sM,iM)
          let rotate slot = case slot of
                M -> R
                L -> M
                R -> L
          if fromEnum iL == pos
            then writeSlot nodes pos M (rotate sL, iL)
            else writeSlot nodes (fromEnum iL) sL (M, toEnum pos)
          if fromEnum iR == pos
            then writeSlot nodes pos L (rotate sR, iR)
            else writeSlot nodes (fromEnum iR) sR (L, toEnum pos)
          if fromEnum iM == pos
            then writeSlot nodes pos R (rotate sM, iM)
            else writeSlot nodes (fromEnum iM) sM (R, toEnum pos)
          else return ()
  doTimes 0 (< MV.length nodes) (+ 1) body

scopeRemove :: MVector s Node -> ST s ()
scopeRemove nodes = do
  let body pos = do
        (b,iM,iL,iR) <- MV.read nodes pos
        let info = readInfoBits b
        if _kind info == Scop
          then do
          let sM = _mainSlot info
          let sL = _leftSlot info
          MV.write nodes pos $ mkScop (toEnum pos) (sL,iL) (sM,iM) 0
          let flip slot = case slot of
                M -> L
                L -> M
                R -> R
          if fromEnum iL == pos
            then writeSlot nodes pos M (flip sL, iL)
            else writeSlot nodes (fromEnum iL) sL (M, toEnum pos)
          if fromEnum iM == pos
            then writeSlot nodes pos L (flip sM, iM)
            else writeSlot nodes (fromEnum iM) sM (L, toEnum pos)
          else return ()
  doTimes 0 (< MV.length nodes) (+ 1) body

loopCut :: MVector s Node -> ST s ()
loopCut nodes = do
  let body pos = do
        (b,_,iL,_) <- MV.read nodes pos
        let info = readInfoBits b
        if _kind info == Abst
          then do
          let sL = _leftSlot info
          writeSlot nodes pos L (L, toEnum pos)
          writeSlot nodes (fromEnum iL) sL (sL, iL)
          else return ()
  doTimes 0 (< MV.length nodes) (+ 1) body

fromNodes :: Vector Node -> Anon
fromNodes nodes = go nodes start 0
  where
    (_,_,start,_) = nodes V.! 0
    len = V.length nodes
    go :: Vector Node -> Word64 -> Integer -> Anon
    go nodes pos dep =
      let
        (b,iM,iL,iR) = nodes V.! (fromEnum pos)
        info = readInfoBits b
        sL   = _leftSlot info
        sR   = _rigtSlot info
        go' i dep = if i == pos then VarA dep else go nodes i dep
      in case _kind info of
        Appl -> AppA (go' iR dep) (go' iL dep)
        Abst -> LamA (go' iR dep)
        Scop -> go' iL (dep + 1)
        Init -> error "Should not happen (INIT)"
        Dupl -> error "Should not happen (DUPL)"

toNetS :: MVector s Node -> ST s (NetS s)
toNetS nodes = do
  fnodes <- V.freeze nodes
  redexes <- newSTRef $ findRedexes fnodes
  frees   <- newSTRef $ findFreeNodes fnodes
  rnodes  <- newSTRef $ nodes
  return $ NetS rnodes frees redexes

decompile :: NetS s -> ST s Anon
decompile net = do
  nodes <- getNodes net
  unwind nodes
  net <- toNetS nodes
  reduce net
  nodes <- getNodes net
  scopeRemove nodes
  net <- toNetS nodes
  reduceNoScop net
  nodes <- getNodes net
  loopCut nodes
  net <- toNetS nodes
  reduceNoScop net
  nodes <- getNodes net >>= V.freeze
  return (fromNodes nodes)

-- churchTwo :: Anon
-- churchTwo = LamA (LamA (AppA (VarA 1) (AppA (VarA 1) (VarA 0))))

-- testCompile :: Net
-- testCompile = compile (AppA churchTwo churchTwo)

-- testReduce :: Net
-- testReduce = fst $ reduce testCompile

-- testDecompile :: Anon
-- testDecompile = decompile testReduce
