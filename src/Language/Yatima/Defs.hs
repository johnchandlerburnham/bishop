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
  { _docsComm :: Text
  , _termAnon :: CID
  , _termMeta :: Meta
  , _typeAnon :: CID
  , _typeMeta :: Meta
  } deriving Show

data Defs = Defs { _index :: Map Name CID
                 , _cache :: Map CID BSL.ByteString
                 } deriving (Show, Eq)

encodeDef :: Def -> Encoding
encodeDef (Def docsComm termAnon termMeta typeAnon typeMeta) = encodeMapLen 6
  <> (encodeString "$0" <> encodeString "Def")
  <> (encodeString "$1" <> encodeString docsComm)
  <> (encodeString "$2" <> encodeCID  termAnon)
  <> (encodeString "$3" <> encodeMeta termMeta)
  <> (encodeString "$4" <> encodeCID  typeAnon)
  <> (encodeString "$5" <> encodeMeta typeMeta)

decodeDef :: Decoder s Def
decodeDef = do
  size     <- decodeMapLen
  failM (size /= 6) ["invalid map size: ", T.pack $ show size]

  decodeCtor "Def" "$0" ["Def"]

  docsComm <- decodeField "Def" "$1" decodeString
  termAnon <- decodeField "Def" "$2" decodeCID
  termMeta <- decodeField "Def" "$3" decodeMeta
  typeAnon <- decodeField "Def" "$4" decodeCID
  typeMeta <- decodeField "Def" "$5" decodeMeta

  return $ Def docsComm termAnon termMeta typeAnon typeMeta

instance Serialise Def where
  encode = encodeDef
  decode = decodeDef

prettyDef :: DefDeref -> Text
prettyDef (DefDeref comm anon meta tyAn tyMe) = T.concat 
  [ (_names tyMe) IM.! 0, "\n"
  , "  : ", prettyTerm $ resaturate tyAn tyMe, "\n"
  , "  = ", prettyTerm $ resaturate anon meta
  ]

indexLookup :: Name -> Defs -> Maybe CID
indexLookup nam ds  = (_index ds) M.!? nam

cacheLookup :: CID -> Defs -> Maybe BSL.ByteString
cacheLookup cid ds = (_cache ds) M.!? cid

deref :: CID -> Defs -> Maybe DefDeref
deref cid ds = do
  (Def c a m ta tm) <- deserialise <$> cacheLookup cid ds :: Maybe Def
  a'  <- deserialise <$> cacheLookup a ds  :: Maybe Anon
  ta' <- deserialise <$> cacheLookup ta ds :: Maybe Anon
  return $ DefDeref c a' m ta' tm

getTerm :: Def -> Defs -> Maybe Term
getTerm (Def docs term_anon term_meta type_anon type_meta) ds  = do
  anon <- deserialise <$> cacheLookup term_anon ds :: Maybe Anon
  return $ resaturate anon term_meta

getTermName :: Def -> Maybe Name
getTermName d = (_names $ _termMeta d) IM.!? 0

prettyDefs :: Defs -> Text
prettyDefs ds = M.foldrWithKey go "" (_index ds)
  where
    go :: Name -> CID -> Text -> Text
    go nam cid txt = case deref cid ds of
      Nothing -> T.concat ["<corrupt index, ",nam,"@",T.pack $ show cid,">"]
      Just d  -> T.concat [txt,"\n",nam,"#",T.pack $ show cid,"\n",prettyDef d, "\n"]
