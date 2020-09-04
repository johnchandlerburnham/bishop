module Language.Bishop.Net where

import           Control.Monad
import           Control.Monad.ST
import           Data.STRef
import           Control.Monad.State.Strict
import           Data.List                  (intercalate)
import           Data.Char                  (ord,chr)
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Data.Bits
import           Data.Vector.Unboxed         (Vector)
import qualified Data.Vector.Unboxed         as V
import           Data.Vector.Unboxed.Mutable (MVector)
import qualified Data.Vector.Unboxed.Mutable as MV
import           Data.Word
import           Text.Printf (PrintfArg, printf)
import           Numeric     (showHex)
import           Debug.Trace

type Node = (Word64, Word64, Word64, Word64)

_info (x,_,_,_) = x
_main (_,x,_,_) = x
_left (_,_,x,_) = x
_rigt (_,_,_,x) = x

data Kind = Init | Appl | Abst | Dupl | Scop -- | Word | Oper | Ifte
  deriving (Enum, Show, Bounded, Eq, Ord)

data Slot = M | L | R deriving (Enum, Show, Bounded, Eq, Ord)

data Info = Info           -- | Size | Bits  |
  { _isFree    :: Bool     -- | 1    | 0:0   |
  , _mainSlot  :: Slot     -- | 2    | 1:2   |
  , _leftSlot  :: Slot     -- | 2    | 3:4   |
  , _rigtSlot  :: Slot     -- | 2    | 5:6   |
  , _kind      :: Kind     -- | 3    | 7:9   |
                           -- | 6    | 10:15 |
  , _meta      :: Word16   -- | 16   | 16:31 |
  , _level     :: Word32   -- | 32   | 32:63 |
  } deriving Show

infoBits :: Info -> Word64
infoBits (Info isFree mainS leftS rigtS kind meta level)  = fromIntegral $
  (fromEnum isFree)             +
  (fromEnum mainS)  `shiftL` 1  +
  (fromEnum leftS)  `shiftL` 3  +
  (fromEnum rigtS)  `shiftL` 5  +
  (fromEnum kind)   `shiftL` 7  +
  (fromEnum meta)   `shiftL` 16 +
  (fromEnum level)  `shiftL` 32

readInfoBits :: Word64 -> Info
readInfoBits x = let n = (fromIntegral x) in Info
  (toEnum $ n               .&. 0x1)
  (toEnum $ (n `shiftR` 1)  .&. 0x3)
  (toEnum $ (n `shiftR` 3)  .&. 0x3)
  (toEnum $ (n `shiftR` 5)  .&. 0x3)
  (toEnum $ (n `shiftR` 7)  .&. 0x7)
  (toEnum $ (n `shiftR` 16) .&. 0xFFFF)
  (toEnum $ (n `shiftR` 32) .&. 0xFFFFFFFF)

instance Enum Info where
  toEnum = readInfoBits . fromIntegral
  fromEnum = fromIntegral . infoBits

printBits :: (PrintfArg a) => a -> IO ()
printBits n = do
  putStrLn $ printf "%08b" n

--mkFree i = (infoBits (Info True M L R Init 0 0),i,i,i)
mkInit i        (lS,l)          = (infoBits (Info False R  lS M  Init 0 0),i,l,i)
mkAppl i (mS,m) (lS,l) (rS,r)   = (infoBits (Info False mS lS rS Appl 0 0),m,l,r)
mkAbst i (mS,m) (lS,l) (rS,r) v = (infoBits (Info False mS lS rS Abst v 0),m,l,r)
mkDupl i (mS,m) (lS,l) (rS,r) v = (infoBits (Info False mS lS rS Dupl 0 v),m,l,r)
mkScop i (mS,m) (lS,l)        v = (infoBits (Info False mS lS R  Scop 0 v),m,l,i)
--mkWord (mS,m) v               = (infoBits (Info False mS N  N  Word 0 0),m,v,0)
--mkOper (mS,m) (lS,l) (rS,r) o = (infoBits (Info False mS lS rS Oper o 0),m,l,r)
--mkIfte (mS,m) (lS,l) (rS,r) o = (infoBits (Info False mS lS rS Ifte o 0),m,l,r)

getInfo :: Node -> Info
getInfo (i,_,_,_) = readInfoBits i

showPort :: Slot -> Word64 -> String
showPort M n = "M" ++ showHex n ""
showPort L n = "L" ++ showHex n ""
showPort R n = "R" ++ showHex n ""

showNode :: (Integer, Node) -> String
showNode (x, (i,m,l,r)) = show x ++ ": " ++ case readInfoBits i of
  (Info True _ _ _ _ _ _)         -> "FREE"
  (Info False _ lS _ Init _ _)    -> "Init " ++ showPort lS l
  (Info False mS lS rS Appl _ _)  -> concat
    ["Appl @ ", showPort mS m, showPort lS l, showPort rS r]
  (Info False mS lS rS Abst v _)  -> concat
    ["Abst ", ['λ', (chr $ fromIntegral v), ' '], showPort mS m, showPort lS l, showPort rS r]
  (Info False mS lS rS Dupl _ v)  -> concat
    ["Dupl let ", showHex v "" ," ",showPort mS m,showPort lS l,showPort rS r]
  (Info False mS lS _ Scop _ v)  -> concat
    ["Scop ( ", showHex v "" , " ",showPort mS m, showPort lS l]
  --(Info False mS lS rS Word _ _)  -> concat
  --  ["Word ", showPort mS m ++ "=" ++ showHex l ""]
  --(Info False mS lS rS Oper v _)  -> concat
  --  ["Oper ", showPort mS m, showPort lS l, showPort rS r, "=", showHex v ""]

  --(Info mS lS rS k) -> concat
  --  [showHex x "",":",show k,"_",showPort mS m,showPort lS l,showPort rS r]

data Net = Net
  { _nodes :: Vector Node
  , _freed :: [Word64]
  , _redex :: [(Word64,Word64)]
  }

instance Show Net where
  show (Net ws fs rs) = concat $
      [ intercalate "\n" (showNode <$> (zip [0..] (V.toList ws)))
      , "\n"
      , "FREE:", show fs
      , "\n"
      , "REDEX:", show rs
      ]

-- Mutable version of Net
data NetS s = NetS
  { _nodesS :: STRef s (MVector s Node)
  , _freedS :: STRef s [Word64]
  , _redexS :: STRef s [(Word64,Word64)]
  }

-- Conversion between mutable and immutable nets
freezeNet :: NetS s -> ST s Net
freezeNet (NetS nodes freed redex) = do
  nodes' <- readSTRef nodes >>= V.freeze
  freed' <- readSTRef freed
  redex' <- readSTRef redex
  return $ Net nodes' freed' redex'

thawNet :: Net -> ST s (NetS s)
thawNet (Net nodes freed redex) = do
  nodes' <- V.thaw nodes >>= newSTRef
  freed' <- newSTRef freed
  redex' <- newSTRef redex
  return $ NetS nodes' freed' redex'

-- Getters, setters and modifiers for NetS
getNode net pos      = do
  nodes <- readSTRef $ _nodesS net
  MV.read nodes (fromEnum pos)
setNode net pos node = do
  nodes <- readSTRef $ _nodesS net
  MV.write nodes (fromEnum pos) node
modifyNode net pos f = do
  nodes <- readSTRef $ _nodesS net
  MV.modify nodes f (fromEnum pos)

getNodes    = readSTRef    . _nodesS
setNodes    = writeSTRef   . _nodesS
modifyNodes = modifySTRef' . _nodesS

getFreed    = readSTRef    . _freedS
setFreed    = writeSTRef   . _freedS
modifyFreed = modifySTRef' . _freedS

getRedex    = readSTRef    . _redexS
setRedex    = writeSTRef   . _redexS
modifyRedex = modifySTRef' . _redexS

growNodes :: NetS s -> Int -> ST s ()
growNodes net l = do
  nodes  <- readSTRef $ _nodesS net
  nodes' <- MV.grow nodes l
  writeSTRef (_nodesS net) nodes'
  
isLoc :: Integral a => a -> Bool
isLoc x = (mod x 4) == 0

findRedexes :: Vector Node -> [(Word64, Word64)]
findRedexes vs = Set.toList $ V.ifoldr insertRedex Set.empty vs
  where
    insertRedex :: Int -> Node -> Set (Word64, Word64) -> Set (Word64, Word64)
    insertRedex i (b,m,l,r) set
      |    _mainSlot (readInfoBits b) == M
        && _mainSlot (readInfoBits b') == M
        && _kind (readInfoBits b)  /= Init
        && _kind (readInfoBits b') /= Init
        && i == fromIntegral m'
        && not (Set.member (m,m') set)
        = Set.insert (m',m) set
      | otherwise = set
        where
         (b',m',l',r')  = vs V.! (fromIntegral m)

isFreed :: NetS s -> Word64 -> ST s Bool
isFreed net i = do
  freed <- getFreed net
  return $ i `elem` freed
  
portDest :: Slot -> Node -> (Slot, Word64)
portDest s (b,m,l,r) =
  let i = readInfoBits b in
  case s of
    M ->  (_mainSlot i,m)
    L ->  (_leftSlot i,l)
    R ->  (_rigtSlot i,r)

getPort :: NetS s -> (Slot, Word64) -> ST s (Slot,Word64)
getPort net (s, n) = do
  node <- getNode net n
  return $ portDest s node

substSlot :: Node -> Slot -> (Slot, Word64) -> Node
substSlot node@(b,m,l,r) x (s,n)  =
  let i = readInfoBits b in
  case x of
    M -> (infoBits $ i { _mainSlot = s }, n, l, r)
    L -> (infoBits $ i { _leftSlot = s }, m, n, r)
    R -> (infoBits $ i { _rigtSlot = s }, m, l, n)

setPort :: NetS s -> Slot -> Word64 -> (Slot,Word64) -> ST s ()
setPort net s i port = do
  node <- getNode net i
  setNode net i (substSlot node s port)

linkPorts :: NetS s -> (Slot,Word64) -> (Slot, Word64) -> ST s ()
linkPorts net (sa,ia) (sb,ib) = do
  setPort net sa ia (sb,ib)
  setPort net sb ib (sa,ia)
  when (sa == M && sb == M) $
    modifyRedex net ((ia,ib) :)

unlinkPort :: NetS s -> (Slot,Word64) -> ST s ()
unlinkPort net (sa,ia) = do
  (sb,ib)   <- getPort net (sa,ia)
  (sa',ia') <- getPort net (sb,ib)
  when (ia' == ia && sa' == sa)
    (setPort net sa ia (sa,ia) >>
     setPort net sb ib (sb,ib))

freeNode :: NetS s -> Word64 -> ST s ()
freeNode net idx = do
  (i,m,l,r) <- getNode net idx
  let (Info _ mS lS lR k meta lvl) = readInfoBits i
  let i' = infoBits (Info True mS lS lR k meta lvl)
  setNode net idx (i',idx,idx,idx)
  modifyFreed net (idx :)

allocNode :: NetS s -> Info -> ST s Word64
allocNode net info = do
  fs <- getFreed net
  let node i = (infoBits info, i, i, i)
  case fs of
    [] -> do
      nodes <- getNodes net
      let i = toEnum (MV.length nodes)
      growNodes net 1
      setNode net i (node i)
      return i
    (f:fs) -> do
      setNode net f (node f)
      setFreed net fs
      return f

-- -- Reduction Rules

annihilate :: NetS s -> (Word64, Word64) -> ST s ()
annihilate net (iA,iB)
  | iA == iB = do
      aLdest <- getPort net (L,iA)
      aRdest <- getPort net (R,iA)
      linkPorts net aLdest aLdest
      linkPorts net aRdest aRdest
      return ()
  | otherwise = do
      aLdest <- getPort net (L,iA)
      bLdest <- getPort net (L,iB)
      linkPorts net aLdest bLdest
      aRdest <- getPort net (R,iA)
      bRdest <- getPort net (R,iB)
      linkPorts net aRdest bRdest
      return ()

annihilateScop :: NetS s -> (Word64, Word64) -> ST s ()
annihilateScop net (iA,iB)
  | iA == iB = do
      aLdest <- getPort net (L,iA)
      linkPorts net aLdest aLdest
      return ()
  | otherwise = do
      aLdest <- getPort net (L,iA)
      bLdest <- getPort net (L,iB)
      linkPorts net aLdest bLdest
      return ()

beta :: NetS s -> (Word64, Word64) -> ST s ()
beta net (iAbst, iAppl) = do
  traceM $ "beta: " ++  concat [show iAbst, ", ", show iAppl]
  abstLDest  <- getPort net (L,iAbst)
  abstRDest  <- getPort net (R,iAbst)
  applLDest  <- getPort net (L,iAppl)
  applRDest  <- getPort net (R,iAppl)
  iP         <- allocNode net (Info False M L R Scop 0 0)
  iQ         <- allocNode net (Info False M L R Scop 0 0)
  linkPorts net (M,iP) applRDest
  linkPorts net (L,iP) abstLDest
  linkPorts net (M,iQ) applLDest
  linkPorts net (L,iQ) abstRDest
  return ()

commute :: NetS s -> (Word64,Kind,Word16,Word32) -> (Word64,Kind,Word16,Word32) -> ST s ()
commute net (iA,kA,mA,lA) (iB,kB,mB,lB) = do
  traceM $ "commute: " ++  concat [show iA, ", ", show iB]
  iP <- allocNode net $ Info False M L R kB mB lB
  iQ <- allocNode net $ Info False M L R kB mB lB
  iR <- allocNode net $ Info False M L R kA mA lA
  iS <- allocNode net $ Info False M L R kA mA lA
  linkPorts net (L,iS) (R,iP)
  linkPorts net (R,iR) (L,iQ)
  linkPorts net (R,iS) (R,iQ)
  linkPorts net (L,iR) (L,iP)
  a1dest <- getPort net (L,iA)
  a2dest <- getPort net (R,iA)
  b1dest <- getPort net (L,iB)
  b2dest <- getPort net (R,iB)
  linkPorts net (M,iP) a1dest
  linkPorts net (M,iQ) a2dest
  linkPorts net (M,iR) b1dest
  linkPorts net (M,iS) b2dest
  return ()

commuteScop :: NetS s -> (Word64,Kind,Word16,Word32) -> (Word64,Kind,Word16,Word32) -> ST s ()
commuteScop net (iA,Scop,mA,lA) (iB,kB,mB,lB) = do
  iP <- allocNode net $ Info False M L R kB   mB lB
  iR <- allocNode net $ Info False M L R Scop mA lA
  iS <- allocNode net $ Info False M L R Scop mA lA
  linkPorts net (L,iS) (R,iP)
  linkPorts net (L,iR) (L,iP)
  a1dest <- getPort net (L,iA)
  b1dest <- getPort net (L,iB)
  b2dest <- getPort net (R,iB)
  linkPorts net (M,iP) a1dest
  linkPorts net (M,iR) b1dest
  linkPorts net (M,iS) b2dest
  return ()
commuteScop net (iA,kA,mA,lA) (iB,kB,mB,lB) = error "commuteScop can only be called on Scop node"

rewrite :: NetS s -> (Word64, Word64) -> ST s ()
rewrite net (iA, iB) = do
  a <- getNode net iA
  b <- getNode net iB
  let free ports = do
        mapM_ (\x -> unlinkPort net (x,iA)) ports >> freeNode net iA
        unless (iA == iB) (mapM_ (\x -> unlinkPort net (x,iB)) ports >> freeNode net iB)
        return ()
  let (Info _ _ _ _ kA mA lA) = getInfo a
  let (Info _ _ _ _ kB mB lB) = getInfo b
  let inc                     = if lA >= lB then 1 else 0

  --traceM $ "reducing: " ++  concat [showNode (fromIntegral iA,a), ", ", showNode (fromIntegral iB,b)]
  --traceM $ "kinds: " ++ (show kA) ++ ", " ++ (show kB)

  case (kA, kB) of
    (Abst, Abst) -> annihilate net (iA,iB)                           >> free [M,L,R]
    (Abst, Appl) -> beta net (iA,iB)           >> free [M,L,R]
    (Abst, Dupl) -> commute net (iA,kA,mA,lA) (iB,kB,mB,lB+1)        >> free [M,L,R]
    (Abst, Scop) -> commuteScop net (iB,kB,mB,lB+1) (iA,kA,mA,lA)    >> free [M,L,R]

    (Appl, Appl) -> annihilate net (iA,iB)                           >> free [M,L,R]
    (Appl, Abst) -> beta net (iB,iA)                                 >> free [M,L,R]
    (Appl, Dupl) -> commute net (iA,kA,mA,lA) (iB,kB,mB,lB)          >> free [M,L,R]
    (Appl, Scop) -> commuteScop net (iB,kB,mB,lB) (iA,kA,mA,lA)      >> free [M,L,R]

    (Dupl, Dupl) -> annihilate net (iA,iB)                           >> free [M,L,R]
    (Dupl, Abst) -> commute net (iA,kA,mA,lA+1) (iB,kB,mB,lB)        >> free [M,L,R]
    (Dupl, Appl) -> commute net (iA,kA,mA,lA) (iB,kB,mB,lB)          >> free [M,L,R]
    -- (Dupl, Scop) -> commuteScop net (iB,kB,mB,lB) (iA,kA,mA,lA+inc)  >> free [M,L,R]

    -- TODO
    -- (Scop, Scop) -> annihilateScop net (iA,iB)                       >> free [M,L,R]
    -- (Scop, Dupl) -> commuteScop net (iA,kA,mA,lA) (iB,kB,mB,lB+inc)  >> free [M,L,R]
    (Scop, Abst) -> commuteScop net (iA,kA,mA,lA+1) (iB,kB,mB,lB)    >> free [M,L,R]
    (Scop, Appl) -> commuteScop net (iA,kA,mA,lA) (iB,kB,mB,lB)      >> free [M,L,R]

reduce :: NetS s -> ST s Int
reduce net = do
  redexes <- findRedexes <$> (getNodes net >>= V.freeze)
  setRedex net redexes
  go net 0
  where
    go net c = do
      redexes <- getRedex net
      case redexes of
        []   -> return c
        r:rs -> do
          rewrite net r
          setRedex net rs
          go net (c + 1)

-- reduceNoScop :: Net -> (Net, Int)
reduceNoScop = reduce -- TODO

reduceFreeze :: Net -> (Net, Int)
reduceFreeze net = runST $ do
  net' <- thawNet net
  i    <- reduce net'
  net  <- freezeNet net'
  return (net, i)

-- makeNet :: [Node] -> Net
-- makeNet nodes = let vs = V.fromList nodes in Net vs [] (findRedexes vs)

-- test_annihilateAbst :: Net
-- test_annihilateAbst = makeNet $
--   [ mkAbst 0 (M,1) (L,2) (L,3) (fromIntegral $ ord 'y')
--   , mkAbst 1 (M,0) (L,4) (L,5) (fromIntegral $ ord 'x')
--   , mkInit 2 (L,0)
--   , mkInit 3 (R,0)
--   , mkInit 4 (L,1)
--   , mkInit 5 (R,1)
--   ]

-- test_annihilateAppl :: Net
-- test_annihilateAppl = makeNet $
--   [ mkAppl 0 (M,1) (L,2) (L,3)
--   , mkAppl 1 (M,0) (L,4) (L,5)
--   , mkInit 2 (L,0)
--   , mkInit 3 (R,0)
--   , mkInit 4 (L,1)
--   , mkInit 5 (R,1)
--   ]

-- test_annihilateDupl :: Net
-- test_annihilateDupl = makeNet $
--   [ mkDupl 0 (M,1) (L,2) (L,3) 0
--   , mkDupl 1 (M,0) (L,4) (L,5) 0
--   , mkInit 2 (L,0)
--   , mkInit 3 (R,0)
--   , mkInit 4 (L,1)
--   , mkInit 5 (R,1)
--   ]

-- test_annihilateScop :: Net
-- test_annihilateScop = makeNet $
--   [ mkScop 0 (M,1) (L,2) 0
--   , mkScop 1 (M,0) (L,3) 0
--   , mkInit 2 (L,0)
--   , mkInit 3 (L,1)
--   ]

-- test_eraseDupl :: Net
-- test_eraseDupl = makeNet $
--   [ mkDupl 0 (M,0) (L,1) (L,2) 0
--   , mkInit 1 (L,0)
--   , mkInit 2 (R,0)
--   ]

-- test_eraseAbst :: Net
-- test_eraseAbst = makeNet $
--   [ mkAbst 0 (M,0) (L,1) (L,2) (fromIntegral $ ord 'x')
--   , mkInit 1 (L,0)
--   , mkInit 2 (R,0)
--   ]

-- test_eraseAppl :: Net
-- test_eraseAppl = makeNet $
--   [ mkAppl 0 (M,0) (L,1) (L,2)
--   , mkInit 1 (L,0)
--   , mkInit 2 (R,0)
--   ]

-- test_eraseScop :: Net
-- test_eraseScop = makeNet $
--   [ mkScop 0 (M,0) (L,1) 0
--   , mkInit 1 (L,0)
--   ]

-- test_betaAbstAppl :: Net
-- test_betaAbstAppl = makeNet $
--   [ mkAbst 0 (M,1) (L,2) (L,3) (fromIntegral $ ord 'x')
--   , mkAppl 1 (M,0) (L,4) (L,5)
--   , mkInit 2 (L,0)
--   , mkInit 3 (R,0)
--   , mkInit 4 (L,1)
--   , mkInit 5 (R,1)
--   ]

-- test_betaApplAbst :: Net
-- test_betaApplAbst = makeNet $
--   [ mkAppl 0 (M,1) (L,2) (L,3)
--   , mkAbst 1 (M,0) (L,4) (L,5) (fromIntegral $ ord 'x')
--   , mkInit 2 (L,0)
--   , mkInit 3 (R,0)
--   , mkInit 4 (L,1)
--   , mkInit 5 (R,1)
--   ]
