module Language.Bishop.Net where

import           Control.Monad.State.Strict
import           Data.List                  (intercalate)
import           Data.Char                  (ord,chr)
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Data.Bits
import qualified Data.Vector.Unboxed        as V
import           Data.Word
import           Text.Printf (PrintfArg, printf)
import           Numeric     (showHex)
import           Debug.Trace

type Node = (Word64, Word64, Word64, Word64)

_info (x,_,_,_) = x
_main (_,x,_,_) = x
_left (_,_,x,_) = x
_rigt (_,_,_,x) = x

data Kind = Init | Appl | Abst | Dupl | Scop {- Word | Oper | Ifte -}
  deriving (Enum, Show, Bounded, Eq, Ord)

data Slot = M | L | R deriving (Enum, Show, Bounded, Eq, Ord)

data Info = Info           --- | Size | Bits  |
  { _isFree    :: Bool     --- | 1    | 0:0   |
  , _mainSlot  :: Slot     --- | 2    | 1:2   |
  , _leftSlot  :: Slot     --- | 2    | 3:4   |
  , _rigtSlot  :: Slot     --- | 2    | 5:6   |
  , _kind      :: Kind     --- | 3    | 7:9   |
                           --- | 6    | 10:15 |
  , _meta      :: Word16   --- | 16   | 16:31 |
  , _level     :: Word32   --- | 32   | 32:63 |
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
  { _nodes :: V.Vector Node
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

isLoc :: Integral a => a -> Bool
isLoc x = (mod x 4) == 0

findRedexes :: V.Vector Node -> [(Word64, Word64)]
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

--testNodes :: [Node]
--testNodes =
--  [ mkAppl (L,1) (L,2) (L,3)
--  , mkInit (M,0)
--  , mkInit (L,0)
--  , mkInit (R,0)
--  ]

makeNet :: [Node] -> Net
makeNet nodes = let vs = V.fromList nodes in Net vs [] (findRedexes vs)

isFreed :: Word64 -> State Net Bool
isFreed i = do
  f <- gets _freed
  return $ i `elem` f

getNode :: Word64 -> State Net Node
getNode i = (\vs -> vs V.! (fromIntegral i)) <$> gets _nodes

getPort :: Slot -> Node -> (Slot, Word64)
getPort s (b,m,l,r) =
  let i = readInfoBits b in
  case s of
    M ->  (_mainSlot i,m)
    L ->  (_leftSlot i,l)
    R ->  (_rigtSlot i,r)

enterPort :: (Slot, Word64) -> State Net (Slot,Word64)
enterPort (s, n) = do
  node <- getNode n
  return $ (getPort s node)

setSlot :: Node -> Slot -> (Slot, Word64) -> Node
setSlot node@(b,m,l,r) x (s,n)  =
  let i = readInfoBits b in
  case x of
    M -> (infoBits $ i { _mainSlot = s }, n, l, r)
    L -> (infoBits $ i { _leftSlot = s }, m, n, r)
    R -> (infoBits $ i { _rigtSlot = s }, m, l, n)

setPort :: Slot -> Word64 -> (Slot,Word64) -> State Net ()
setPort s i port = do
  node <- ((\x -> x V.! (fromIntegral i)) <$> gets _nodes)
  modify $ \n ->
    n { _nodes = (_nodes n) V.// [(fromIntegral i, (setSlot node s port))] }

linkPorts :: (Slot,Word64) -> (Slot, Word64) -> State Net ()
linkPorts (sa,ia) (sb,ib) = do
  setPort sa ia $ (sb,ib)
  setPort sb ib $ (sa,ia)
  when (sa == M && sb == M) $
   modify (\n -> n { _redex = (ia, ib) : _redex n })

unlinkPort :: (Slot,Word64) -> State Net ()
unlinkPort (sa,ia) = do
  (sb,ib) <- enterPort (sa,ia)
  (sa',ia') <- enterPort (sb,ib)
  if (ia' == ia && sa' == sa) then do
      setPort sa ia (sa,ia)
      setPort sb ib (sb,ib)
    else return ()

freeNode :: Word64 -> State Net ()
freeNode idx = do
  nodes <- gets _nodes
  case nodes V.!? (fromIntegral idx) of 
    Nothing -> return ()
    Just (i,m,l,r)  -> do
      let (Info _ mS lS lR k meta lvl) = (readInfoBits i)
      let i' = infoBits (Info True mS lS lR k meta lvl)
      modify (\n ->
        n { _nodes = (_nodes n) V.// [(fromIntegral idx,(i',idx,idx,idx))]
          , _freed = idx:(_freed n)
          })

allocNode :: Info -> State Net Word64
allocNode info = do
  (Net vs fs rs) <- get
  let node i = (infoBits info, i, i, i)
  case fs of
    [] -> do
      let i = fromIntegral (V.length vs)
      modify (\n -> n { _nodes = vs `V.snoc` (node i)})
      return i
    (f:fs) -> do
      modify (\n -> n { _nodes = vs V.// [(fromIntegral f,node f)], _freed = fs})
      return f

-- Reduction Rules

annihilate :: (Word64, Word64) -> State Net ()
annihilate (iA,iB)
  | iA == iB = do
      aLdest <- enterPort (L,iA)
      aRdest <- enterPort (R,iA)
      linkPorts aLdest aLdest
      linkPorts aRdest aRdest
      return ()
  | otherwise = do
      aLdest <- enterPort (L,iA)
      bRdest <- enterPort (R,iB)
      linkPorts aLdest bRdest
      aRdest <- enterPort (R,iA)
      bLdest <- enterPort (L,iB)
      linkPorts aRdest bLdest
      return ()

annihilateScop :: (Word64, Word64) -> State Net ()
annihilateScop (iA,iB) 
  | iA == iB = do
      aLdest <- enterPort (L,iA)
      linkPorts aLdest aLdest
      return ()
  | otherwise = do
      aLdest <- enterPort (L,iA)
      bLdest <- enterPort (L,iB)
      linkPorts aLdest bLdest
      return ()

beta :: (Word64, Word64) -> State Net ()
beta (iAbst, iAppl) = do
  traceM $ "beta: " ++  concat [show iAbst, ", ", show iAppl]
  abstLDest  <- enterPort (L,iAbst)
  abstRDest  <- enterPort (R,iAbst)
  applLDest  <- enterPort (L,iAppl)
  applRDest  <- enterPort (R,iAppl)
  iP         <- allocNode (Info False M L R Scop 0 0)
  iQ         <- allocNode (Info False M L R Scop 0 0)
  linkPorts (M,iP) applRDest
  linkPorts (L,iP) abstLDest
  linkPorts (M,iQ) applLDest
  linkPorts (L,iQ) abstRDest
  return ()

commute :: (Word64,Kind,Word16,Word32) -> (Word64,Kind,Word16,Word32) -> State Net ()
commute (iA,kA,mA,lA) (iB,kB,mB,lB) = do
  traceM $ "commute: " ++  concat [show iA, ", ", show iB]
  iP <- allocNode $ Info False M L R kB mB lB
  iQ <- allocNode $ Info False M L R kB mB lB
  iR <- allocNode $ Info False M L R kA mA lA
  iS <- allocNode $ Info False M L R kA mA lA
  linkPorts (L,iS) (R,iP)
  linkPorts (R,iR) (L,iQ)
  linkPorts (R,iS) (R,iQ)
  linkPorts (L,iR) (L,iP)
  a1dest <- enterPort (L,iA)
  a2dest <- enterPort (R,iA)
  b1dest <- enterPort (L,iB)
  b2dest <- enterPort (R,iB)
  linkPorts (M,iP) a1dest
  linkPorts (M,iQ) a2dest
  linkPorts (M,iR) b1dest
  linkPorts (M,iS) b2dest
  return ()

commuteScop :: (Word64,Kind,Word16,Word32) -> (Word64,Kind,Word16,Word32) -> State Net ()
commuteScop (iA,Scop,mA,lA) (iB,kB,mB,lB) = do
  iP <- allocNode $ Info False M L R kB   mB lB
  iR <- allocNode $ Info False M L R Scop mA lA
  iS <- allocNode $ Info False M L R Scop mA lA
  linkPorts (L,iS) (R,iP)
  linkPorts (L,iR) (L,iP)
  a1dest <- enterPort (L,iA)
  b1dest <- enterPort (L,iB)
  b2dest <- enterPort (R,iB)
  linkPorts (M,iP) a1dest
  linkPorts (M,iR) b1dest
  linkPorts (M,iS) b2dest
  return ()
commuteScop (iA,kA,mA,lA) (iB,kB,mB,lB) = error "commuteScop can only be called on Scop node"

rewrite :: (Word64, Word64) -> State Net ()
rewrite (iA, iB) = do
  nodes <- gets $ _nodes
  let a = nodes V.! (fromIntegral iA)
  let b = nodes V.! (fromIntegral iB)
  let free ports = do
        mapM_ (\x -> unlinkPort (x,iA)) ports >> freeNode iA
        unless (iA == iB) (mapM_ (\x -> unlinkPort (x,iB)) ports >> freeNode iB)
        return ()
  let (Info _ _ _ _ kA mA lA) = getInfo a
  let (Info _ _ _ _ kB mB lB) = getInfo b
  let inc                     = if lA >= lB then 1 else 0

  --traceM $ "reducing: " ++  concat [showNode (fromIntegral iA,a), ", ", showNode (fromIntegral iB,b)]
  --traceM $ "kinds: " ++ (show kA) ++ ", " ++ (show kB)

  case (kA, kB) of
    (Abst, Abst) -> annihilate (iA,iB)                           >> free [M,L,R]
    (Abst, Appl) -> beta (iA,iB)           >> free [M,L,R]
    (Abst, Dupl) -> commute (iA,kA,mA,lA) (iB,kB,mB,lB+1)        >> free [M,L,R]
    (Abst, Scop) -> commuteScop (iB,kB,mB,lB+1) (iA,kA,mA,lA)    >> free [M,L,R]

    (Appl, Appl) -> annihilate (iA,iB)                           >> free [M,L,R]
    (Appl, Abst) -> beta (iB,iA)                                 >> free [M,L,R]
    (Appl, Dupl) -> commute (iA,kA,mA,lA) (iB,kB,mB,lB)          >> free [M,L,R]
    (Appl, Scop) -> commuteScop (iB,kB,mB,lB) (iA,kA,mA,lA)      >> free [M,L,R]

    (Dupl, Dupl) -> annihilate (iA,iB)                           >> free [M,L,R]
    (Dupl, Abst) -> commute (iA,kA,mA,lA+1) (iB,kB,mB,lB)        >> free [M,L,R]
    (Dupl, Appl) -> commute (iA,kA,mA,lA) (iB,kB,mB,lB)          >> free [M,L,R]
    (Dupl, Scop) -> commuteScop (iB,kB,mB,lB) (iA,kA,mA,lA+inc)  >> free [M,L,R]

    (Scop, Scop) -> annihilateScop (iA,iB)                       >> free [M,L,R]
    (Scop, Dupl) -> commuteScop (iA,kA,mA,lA) (iB,kB,mB,lB+inc)  >> free [M,L,R]
    (Scop, Abst) -> commuteScop (iA,kA,mA,lA+1) (iB,kB,mB,lB)    >> free [M,L,R]
    (Scop, Appl) -> commuteScop (iA,kA,mA,lA) (iB,kB,mB,lB)      >> free [M,L,R]

reduce :: Net -> (Net, Int)
reduce x = go (x {_redex = (findRedexes (_nodes x))}) 0
  where
    go n c = case _redex n of
      []   -> (n, c)
      r:rs -> go (execState (rewrite r) (n { _redex = rs })) (c + 1)

test_annihilateAbst :: Net
test_annihilateAbst = makeNet $
  [ mkAbst 0 (M,1) (L,2) (L,3) (fromIntegral $ ord 'y')
  , mkAbst 1 (M,0) (L,4) (L,5) (fromIntegral $ ord 'x')
  , mkInit 2 (L,0)
  , mkInit 3 (R,0)
  , mkInit 4 (L,1)
  , mkInit 5 (R,1)
  ]

test_annihilateAppl :: Net
test_annihilateAppl = makeNet $
  [ mkAppl 0 (M,1) (L,2) (L,3)
  , mkAppl 1 (M,0) (L,4) (L,5)
  , mkInit 2 (L,0)
  , mkInit 3 (R,0)
  , mkInit 4 (L,1)
  , mkInit 5 (R,1)
  ]

test_annihilateDupl :: Net
test_annihilateDupl = makeNet $
  [ mkDupl 0 (M,1) (L,2) (L,3) 0
  , mkDupl 1 (M,0) (L,4) (L,5) 0
  , mkInit 2 (L,0)
  , mkInit 3 (R,0)
  , mkInit 4 (L,1)
  , mkInit 5 (R,1)
  ]

test_annihilateScop :: Net
test_annihilateScop = makeNet $
  [ mkScop 0 (M,1) (L,2) 0
  , mkScop 1 (M,0) (L,3) 0
  , mkInit 2 (L,0)
  , mkInit 3 (L,1)
  ]

test_eraseDupl :: Net
test_eraseDupl = makeNet $
  [ mkDupl 0 (M,0) (L,1) (L,2) 0
  , mkInit 1 (L,0)
  , mkInit 2 (R,0)
  ]

test_eraseAbst :: Net
test_eraseAbst = makeNet $
  [ mkAbst 0 (M,0) (L,1) (L,2) (fromIntegral $ ord 'x')
  , mkInit 1 (L,0)
  , mkInit 2 (R,0)
  ]

test_eraseAppl :: Net
test_eraseAppl = makeNet $
  [ mkAppl 0 (M,0) (L,1) (L,2)
  , mkInit 1 (L,0)
  , mkInit 2 (R,0)
  ]

test_eraseScop :: Net
test_eraseScop = makeNet $
  [ mkScop 0 (M,0) (L,1) 0
  , mkInit 1 (L,0)
  ]

test_betaAbstAppl :: Net
test_betaAbstAppl = makeNet $
  [ mkAbst 0 (M,1) (L,2) (L,3) (fromIntegral $ ord 'x')
  , mkAppl 1 (M,0) (L,4) (L,5)
  , mkInit 2 (L,0)
  , mkInit 3 (R,0)
  , mkInit 4 (L,1)
  , mkInit 5 (R,1)
  ]

test_betaApplAbst :: Net
test_betaApplAbst = makeNet $
  [ mkAppl 0 (M,1) (L,2) (L,3)
  , mkAbst 1 (M,0) (L,4) (L,5) (fromIntegral $ ord 'x')
  , mkInit 2 (L,0)
  , mkInit 3 (R,0)
  , mkInit 4 (L,1)
  , mkInit 5 (R,1)
  ]

