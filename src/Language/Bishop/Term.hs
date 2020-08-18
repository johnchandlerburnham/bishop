{-# LANGUAGE DataKinds   #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTSyntax  #-}
{-# LANGUAGE ScopedTypeVariables  #-}
module Language.Bishop.Term where

import           Data.Char
import           Data.IntMap                (IntMap)
import qualified Data.IntMap                as IM
import           Data.Map                   (Map)
import qualified Data.Map                   as M
import           Data.Text                  (Text)
import qualified Data.Text                  as T hiding (find)
import qualified Data.Text.Encoding         as T
import qualified Data.Text.Read             as T
import           Data.Word

import qualified Data.ByteString.Lazy       as BSL
import           Data.ByteString            (ByteString)
import qualified Data.ByteString            as BS
import qualified Data.ByteString.Builder    as Build
import qualified Data.ByteString.Multibase  as MB
import qualified Data.ByteString.BaseN      as BaseN
import qualified Data.ByteString.Base16     as BS16
import qualified Data.ByteString.Base16     as BS16

import           Control.Monad.State.Strict
import           Control.Monad.Trans.Except

import           Codec.Serialise
import           Codec.Serialise.Decoding
import           Codec.Serialise.Encoding

import           Data.IPLD.CID              (CID)
import qualified Data.IPLD.CID              as CID
import qualified Data.Multihash             as MH
import qualified Crypto.Hash as C

import           Prelude                    hiding (print)

type Name = Text

data Term where
  Var :: Name -> Integer -> Term
  Lam :: Name -> Term -> Term
  App :: Term -> Term -> Term
  Ref :: Name -> CID -> Term
  deriving Eq

-- Printer
prettyTerm :: Term -> Text
prettyTerm t = go t
  where
    go :: Term -> Text
    go t = case t of
      Var n i -> n
      Ref n h -> n
      Lam n b -> T.concat ["|",n, printLams b]
      App f a -> printApps f a

    printLams :: Term -> Text
    printLams (Lam n b) = T.concat [",", n, printLams b]
    printLams x         = T.concat ["| ", go x]

    printApps :: Term -> Term -> Text
    printApps f@(Lam n b) a  = T.concat ["(", go f, ") ", go a]
    printApps f  a@(Lam n b) = T.concat [go f, " (", go a, ")"]
    printApps f (App af aa)  = T.concat [go f, " ", "(", printApps af aa,")"]
    printApps (App af aa) a  = T.concat [printApps af aa, " ", go a]
    printApps f a            = T.concat [go f, " ", go a]

instance Show Term where
  show t = T.unpack $ prettyTerm t

data Anon where
  VarA :: Integer  -> Anon
  LamA :: Anon -> Anon
  AppA :: Anon -> Anon -> Anon
  RefA :: CID -> Anon
  deriving (Show, Eq)


encodeCID :: CID -> Encoding
encodeCID cid =
  let cid_bytestring = BSL.toStrict $ Build.toLazyByteString $ CID.buildCid cid
      cid_atBaseID   = BaseN.encodeAtBase BaseN.BaseIdentity cid_bytestring
      cid_multibase  = MB.fromMultibase $ MB.encode cid_atBaseID
   in encodeTag 42 <> encodeBytes cid_multibase

testCID :: CID
testCID = 
  let txt = "bafy2bzacec6hkz4zx3vaeistmyydg52wp4inamrsk7jblhi7ohit7xcpzl5co" in
  case CID.cidFromText txt of
    Right a -> a
    Left  a -> error "bad"

cidToBase :: (MB.ToCode b) => BaseN.Base b -> CID -> ByteString
cidToBase base cid =
  let cid_bytestring = BSL.toStrict $ Build.toLazyByteString $ CID.buildCid cid
      cid_atBase     = BaseN.encodeAtBase base cid_bytestring
      cid_multibase  = MB.fromMultibase $ MB.encode cid_atBase
    in cid_multibase

cidToBytes :: CID -> ByteString
cidToBytes cid = BSL.toStrict $ Build.toLazyByteString $ CID.buildCid cid

cidFromBase :: ByteString -> Either String CID
cidFromBase bs = do
  mb  <- MB.decode bs
  cid <- CID.decodeCid mb
  return cid

decodeCID :: Decoder s CID
decodeCID = do
  tag   <- decodeTag
  if tag /= 42
  then fail "CBOR Link tag not equal to 42"
  else do
    base <- decodeBytes
    case cidFromBase base of
      Left str -> fail $ "CID decoding error: " ++ str
      Right cid -> return cid

instance Serialise CID where
  encode = encodeCID
  decode = decodeCID

encodeAnon :: Anon -> Encoding
encodeAnon term = case term of
  VarA idx     -> encodeMapLen 2
                  <> (encodeString "ctor" <> encodeString "Var")
                  <> (encodeString "fld1" <> encodeInteger idx)
  LamA bdy     -> encodeMapLen 2
                  <> (encodeString "ctor" <> encodeString "Lam")
                  <> (encodeString "fld1" <> encodeAnon    bdy)
  AppA fun arg -> encodeMapLen 3
                  <> (encodeString "ctor" <> encodeString "App")
                  <> (encodeString "fld1" <> encodeAnon    fun)
                  <> (encodeString "fld2" <> encodeAnon    arg)
  RefA cid     -> encodeMapLen 2
                  <> (encodeString "ctor" <> encodeString "Ref")
                  <> (encodeString "fld1" <> encodeCID     cid)

failM :: (Monad m, MonadFail m) => Bool -> Text -> m ()
failM c msg = if c then fail (T.unpack msg) else return ()

decodeAnon :: Decoder s Anon
decodeAnon = do
  size <- decodeMapLen
  case size of
    2 -> do
      field <- decodeString
      failM (field /= "ctor") (T.concat ["invalid top field: ", field])
      ctor <- decodeString
      case ctor of
        "Var" -> do
           field <- decodeString
           failM (field /= "fld1") (T.concat ["invalid Var field: ", field])
           indx <- decodeInteger
           return $ VarA indx
        "Lam" -> do
           field <- decodeString
           failM (field /= "fld1") (T.concat ["invalid Lam field: ", field])
           body <- decodeAnon
           return $ LamA body
        "Ref" -> do
           field <- decodeString
           failM (field /= "fld1") (T.concat ["invalid Ref field: ", field])
           link <- decode
           return $ RefA link
        _ -> fail $ "invalid ctor: " ++ T.unpack ctor
    3 -> do
      field <- decodeString
      failM (field /= "ctor") (T.concat ["invalid top field: ", field])
      ctor <- decodeString
      case ctor of
        "App" -> do
           field <- decodeString
           failM (field /= "fld1") (T.concat ["invalid App field: ", field])
           func <- decodeAnon
           field <- decodeString
           failM (field /= "fld2") (T.concat ["invalid App field: ", field])
           argm <- decodeAnon
           return $ AppA func argm
    _ -> fail "invalid map size"

instance Serialise Anon where
  encode = encodeAnon
  decode = decodeAnon

testTerm = LamA $ (VarA 0)

hashlazyWith :: C.HashAlgorithm alg => alg -> BSL.ByteString -> C.Digest alg
hashlazyWith _ bs = C.hashlazy bs

mkCborCIDv1 :: (MH.Multihashable alg, Serialise a) => alg -> a -> CID
mkCborCIDv1 alg a = CID.newCidV1 CID.DagCbor (hashlazyWith alg (serialise a))

makeCID :: Serialise a => a -> CID
makeCID a = mkCborCIDv1 C.Blake2b_256 a

--cid1 = anonCID testTerm

--testTerm2 = AppA testTerm (RefA cid1)

data Meta = Meta { _names :: IntMap Name } deriving (Show,Eq)

encodeMeta :: Meta -> Encoding
encodeMeta (Meta ns) =
  encodeString "Meta" <> encodeMapLen 1
    <> (encodeString "names" <> encode ns)

decodeMeta :: Decoder s Meta
decodeMeta = do
  field <- decodeString
  failM (field /= "Meta") (T.concat ["invalid top field: ", field])
  size <- decodeMapLen
  failM (size /= 1) (T.concat ["invalid map size: ", T.pack $ show size])
  field <- decodeString
  failM (field /= "names") (T.concat ["invalid Meta field: ", field])
  ns   <- decode
  return $ Meta ns

instance Serialise Meta where
  encode = encodeMeta
  decode = decodeMeta

data Def = Def { _term :: CID, _meta :: CID } deriving Show

encodeDef :: Def -> Encoding
encodeDef (Def t m) =
  encodeString "Def" <> encodeMapLen 2
    <> (encodeString "term" <> encodeCID t)
    <> (encodeString "meta" <> encodeCID m)

decodeDef :: Decoder s Def
decodeDef = do
  field <- decodeString
  failM (field /= "Def") (T.concat ["invalid top field: ", field])
  size <- decodeMapLen
  failM (size /= 2) (T.concat ["invalid map size: ", T.pack $ show size])
  field <- decodeString
  failM (field /= "term") (T.concat ["invalid Def field: ", field])
  term  <- decodeCID
  field <- decodeString
  failM (field /= "meta") (T.concat ["invalid Def field: ", field])
  meta  <- decodeCID
  return $ Def term meta

instance Serialise Def where
  encode = encodeDef
  decode = decodeDef

data Defs = Defs { _index :: Map Name CID
                 , _cache :: Map CID BSL.ByteString
                 } deriving (Show, Eq)

unname :: Name -> Term -> (Anon,Meta)
unname n t = let (a,(nm,_)) = runState (go t) (init,1) in (a,nm)
  where
    init = Meta $ IM.singleton 0 n
    go :: Term -> State (Meta,Int) Anon
    go (Var n idx) = return (VarA idx)
    go (Lam n b) = do
      modify (\(Meta m,i) -> (Meta $ IM.insert i n m, i+1))
      b' <- go b
      return $ LamA b'
    go (App f a) = do
      f <- go f
      a <- go a
      return $ AppA f a
    go (Ref n hsh) = return (RefA hsh)

findName :: Integer -> [Name] -> Maybe Name
findName i cs = go cs 0
  where
    go (c:cs) j
      | i == j   = Just c
      | otherwise = go cs (j+1)
    go [] _     = Nothing

rename :: Anon -> Meta -> Defs -> Term
rename anon meta ds = fst $ runState (go anon [defName meta]) (meta,1)
  where
    defName (Meta ns) = ns IM.! 0
    go :: Anon -> [Name] -> State (Meta,Int) Term
    go t ctx = case t of
      VarA idx -> case findName idx ctx of
        Just n  -> return (Var n idx)
        Nothing -> return (Var "" idx)
      LamA b    -> do
        (Meta m,i) <- get
        let n = maybe "" id (IM.lookup i m)
        put (Meta m, i+1)
        b' <- go b (n:ctx)
        return $ Lam n b'
      AppA f a   -> App <$> (go f ctx) <*> (go a ctx)
      RefA cid   -> case (_cache ds) M.!? cid of
        Nothing -> return (Ref "" cid)
        Just en -> do
           let Def _ meta = deserialise en :: Def
           case (_cache ds) M.!? meta of
             Nothing -> return (Ref "" cid)
             Just en -> do 
               let Meta m = deserialise en :: Meta
               return (Ref (m IM.! 0) cid)

getTerm :: Def -> Defs -> Maybe Term
getTerm (Def term_cid meta_cid) ds  = do
  anon <- _cache ds M.!? term_cid
  meta <- _cache ds M.!? meta_cid
  return $ rename (deserialise anon) (deserialise meta) ds

getName :: Def -> Defs -> Maybe Name
getName (Def term_cid meta_cid) ds = do
  meta <- _cache ds M.!? meta_cid
  (_names $ deserialise meta) IM.!? 0

deref :: CID -> Defs -> Maybe Term
deref cid ds = do
  def_bytes <- _cache ds M.!? cid
  getTerm (deserialise def_bytes) ds

indexLookup :: Name -> Defs -> Maybe Def
indexLookup nam ds  = do
  cid       <- (_index ds) M.!? nam
  def_bytes <- _cache ds M.!? cid
  return (deserialise def_bytes)

prettyDef :: CID -> Def -> Defs -> Text
prettyDef cid (Def term_cid meta_cid) ds@(Defs _ cache) = 
  case (cache M.!? term_cid, cache M.!? meta_cid) of
  (Just x, Just y) -> 
    let anon = deserialise x :: Anon
        meta = deserialise y :: Meta
     in T.concat [ (_names meta) IM.! 0, "@", T.pack (show cid), " =\n  "
                 , prettyTerm $ rename anon meta ds
                 ]
  _ -> ""

prettyDefs :: Defs -> Text
prettyDefs ds = M.foldrWithKey go "" (_index ds)
  where
    go :: Name -> CID -> Text -> Text
    go nam cid txt = case _cache ds M.!? cid of
      Nothing -> ""
      Just d  -> T.concat [txt, "\n", prettyDef cid (deserialise d :: Def) ds]
