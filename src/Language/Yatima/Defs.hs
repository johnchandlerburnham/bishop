{-# LANGUAGE ScopedTypeVariables #-}
module Language.Yatima.Defs 
  ( Def(..)
  , Defs(..)
  , DefDeref(..)
  , encodeDef
  , decodeDef
  , indexLookup
  , cacheLookup
  , deref
  , getTerm
  , getTermName
  , prettyDefs
  ) where

import           Data.Text                  (Text)
import qualified Data.Text                  as T hiding (find)
import           Data.IntMap                (IntMap)
import qualified Data.IntMap                as IM
import           Data.Map                   (Map)
import qualified Data.Map                   as M

import qualified Data.ByteString.Lazy       as BSL
import           Data.ByteString            (ByteString)
import           Data.Proxy

import           Codec.Serialise
import           Codec.Serialise.Decoding
import           Codec.Serialise.Encoding

import           Data.IPLD.CID              (CID)
import qualified Data.IPLD.CID              as CID

import Language.Yatima.Term

data DefDeref = DefDeref Text Anon Meta Anon Meta

-- A Definition, but with fields replaced by content ids
data Def = Def
  { _docsComm :: CID
  , _termAnon :: CID
  , _termMeta :: CID
  , _typeAnon :: CID
  , _typeMeta :: CID
  } deriving Show

data Defs = Defs { _index :: Map Name CID
                 , _cache :: Map CID BSL.ByteString
                 } deriving (Show, Eq)

encodeDef :: Def -> Encoding
encodeDef (Def docsComm termAnon termMeta typeAnon typeMeta) = encodeMapLen 6
  <> (encodeString "$0" <> encodeString "Def")
  <> (encodeString "$1" <> encodeCID docsComm)
  <> (encodeString "$2" <> encodeCID termAnon)
  <> (encodeString "$3" <> encodeCID termMeta)
  <> (encodeString "$4" <> encodeCID typeAnon)
  <> (encodeString "$5" <> encodeCID typeMeta)

decodeDef :: Decoder s Def
decodeDef = do
  size     <- decodeMapLen
  failM (size /= 6) ["invalid map size: ", T.pack $ show size]

  decodeCtor "Def" "$0" ["Def"]

  docsComm <- decodeField "Def" "$1" decodeCID
  termAnon <- decodeField "Def" "$2" decodeCID
  termMeta <- decodeField "Def" "$3" decodeCID
  typeAnon <- decodeField "Def" "$4" decodeCID
  typeMeta <- decodeField "Def" "$5" decodeCID

  return $ Def docsComm termAnon termMeta typeAnon typeMeta

instance Serialise Def where
  encode = encodeDef
  decode = decodeDef

prettyDef :: DefDeref -> Text
prettyDef (DefDeref comm anon meta tyAn tyMe) = T.concat 
  [ (_names tyMe) IM.! 0, " : ", prettyTerm $ resaturate tyAn tyMe, "\n"
  , (_names meta) IM.! 0, " = ", prettyTerm $ resaturate anon meta
  ]

indexLookup :: Name -> Defs -> Maybe CID
indexLookup nam ds  = (_index ds) M.!? nam

cacheLookup :: CID -> Defs -> Maybe BSL.ByteString
cacheLookup cid ds = (_cache ds) M.!? cid

deref :: CID -> Defs -> Maybe DefDeref
deref cid ds = do
  (Def c a m ta tm) <- deserialise <$> cacheLookup cid ds :: Maybe Def
  c'  <- deserialise <$> cacheLookup c ds  :: Maybe Text
  a'  <- deserialise <$> cacheLookup a ds  :: Maybe Anon
  m'  <- deserialise <$> cacheLookup m ds  :: Maybe Meta
  ta' <- deserialise <$> cacheLookup ta ds :: Maybe Anon
  tm' <- deserialise <$> cacheLookup tm ds :: Maybe Meta
  return $ DefDeref c' a' m' ta' tm'

getTerm :: Def -> Defs -> Maybe Term
getTerm (Def docs term_anon term_meta type_anon type_meta) ds  = do
  anon <- deserialise <$> cacheLookup term_anon ds :: Maybe Anon
  meta <- deserialise <$> cacheLookup term_meta ds :: Maybe Meta
  return $ resaturate anon meta

getTermName :: Def -> Defs -> Maybe Name
getTermName (Def docs term_anon term_meta type_anon type_meta) ds  = do
  meta <- deserialise <$> cacheLookup term_meta ds :: Maybe Meta
  (_names meta) IM.!? 0

prettyDefs :: Defs -> Text
prettyDefs ds = M.foldrWithKey go "" (_index ds)
  where
    go :: Name -> CID -> Text -> Text
    go nam cid txt = case deref cid ds of
      Nothing -> T.concat ["<corrupt index, ",nam,"@",T.pack $ show cid,">"]
      Just d  -> T.concat [txt,"\n",nam," @ ",T.pack $ show cid,"\n",prettyDef d]
