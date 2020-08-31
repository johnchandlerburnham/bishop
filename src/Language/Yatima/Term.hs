{-# LANGUAGE DataKinds   #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTSyntax  #-}
{-# LANGUAGE TupleSections  #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-|
Module      : Language.Yatima.Term
Description : Defines expressions in the Yatima language
Copyright   : (c) Sunshine Cybernetics, 2020
License     : AGPL-3
Maintainer  : john@sunshinecybernetics.com
Stability   : experimental

This module defines `Term`, the type of expressions in the Yatima language, as
well as its serialisation and deserialisation. We do not implement `Serialise`
instances for `Term` directly, rather we first strip out naming and source
location metadata `Meta` and then independently serialise the metadata and the
name-free, anonymous term `Anon`. This is done so that the content addresses of
terms which differ only in source layout and naming will be equal (and thus
shared).

The transformation from `Term` to pairs of `Anon` and `Meta` is handled by then
`rename` and `unname` functions.

All `Serialise` instances have encoding and decoding functions designed to match
the [js-ipld-dag-cbor](https://github.com/ipld/js-ipld-dag-cbor) libraries
encoding of an isomorphic JSON representation of `Anon` terms. This has been
implemented by hand (rather than using existing JSON libraries such as Aeson) so
as to replace all occurrences of IPFS `CID` types with the CBOR tag 42 expected
by [IPLD](https://ipld.io)
-}
module Language.Yatima.Term
  ( -- * Re-exported modules
    -- | Quantitative type theory usage semirig
    module Language.Yatima.Uses
    -- | Primitve numeric operations
  , module Language.Yatima.Prim
    -- | IPFS content-identifiers
  , module Language.Yatima.CID
  , Name(..)
  , Loc(..)
  , noLoc
  , Term(..)
  , prettyTerm
  , Anon(..)
  , Meta(..)
  , desaturate
  , resaturate
  , decodeField
  , decodeCtor
  , failM
  , encodeAnon
  , decodeAnon
  , encodeMeta
  , decodeMeta
  , encodeLoc
  , decodeLoc
  ) where

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

import           Control.Monad.State.Strict
import           Control.Monad.Trans.Except

import           Codec.Serialise
import           Codec.Serialise.Decoding
import           Codec.Serialise.Encoding

import           Data.IPLD.CID              (CID)
import qualified Data.IPLD.CID              as CID

import           Language.Yatima.Uses
import           Language.Yatima.Prim
import           Language.Yatima.CID
import           Prelude                    hiding (print)


-- * Yatima expressions

-- | An abstract name used in Yatima term for parsing and printing
type Name = Text

-- | A source code location
data Loc = Loc {_from :: Int, _upto :: Int} deriving (Show,Eq)

-- | Negative locations are nonsensical and indicate the absense of Location.
-- The reason for doing this instead of Maybe is to simplify serialisation.
noLoc = Loc (-1) (-1)

-- | A Yatima term with names and source locations
data Term where
  -- | Local variable implemented via De Bruijn indices
  Var :: Loc -> Name -> Int -> Term
  -- | Global immutable IPFS-compatible content-addressed reference
  Ref :: Loc -> Name -> CID -> Term
  -- | A typed lambda with usage semirig a la Quantiative Type Theory
  Lam :: Loc -> Name -> Maybe (Uses,Term) -> Term -> Term
  -- | An application of a function to an argument
  App :: Loc -> Term -> Term -> Term
  -- | An inline local definition, this also requires type and usage information
  Let :: Loc -> Name -> Uses -> Term -> Term -> Term -> Term
  -- | The type of types. Note that this causes `Term` to admit paradoxes via 
  -- Gerards Paradox, and makes it unsuitable for safe theorem prooving. A
  -- future version of Yatima will likely remove @ Type : Type @
  Typ :: Loc -> Term
  -- | The universal quantifier: forall.
  All :: Loc -> Name -> Uses -> Term -> Term -> Term
  -- | The type of self-types, i.e. types which can depend on the value being
  -- typed.
  Slf :: Loc -> Name -> Term -> Term
  -- | Self-type introduction. Wrap a lambda-encoding as a datatype
  New :: Loc -> Term -> Term -> Term
  -- | Self-type elimination. Turn a datatype into a lambda encoding.
  Eli :: Loc -> Term -> Term
  -- | Primitive words designed to match WASM i64 values
  Wrd :: Loc -> Word64 -> Term
  -- | The type of words
  I64 :: Loc -> Term
  -- | Primitive floats, designed to match WASM f64 values
  Dbl :: Loc -> Double -> Term
  -- | The type of floats
  F64 :: Loc -> Term
  -- | Primitive operations on words and floats defined in
  -- "Language.Yatima.Prim", designed to match WASM arithmetic operations
  Opr :: Loc -> Prim -> Term -> Term -> Term
  -- | Primitive if-then-else on Words, this is necessary to allow the
  -- "Language.Yatima.Net" interaction net runtime to branch on words
  Ite :: Loc -> Term -> Term -> Term -> Term

-- | Pretty-printer for terms
prettyTerm :: Term -> Text
prettyTerm t = go t
  where
    uses :: Uses -> Text
    uses Zero = "0 "
    uses Once = "1 "
    uses Many = ""

    name "" = "_"
    name x  = x

    go :: Term -> Text
    go t = case t of
      Var _ n i -> n
      Ref _ n h -> n
      Lam _ n ut b    -> T.concat ["λ", lams n ut b]
      Let _ n u t x b -> T.concat ["let ",uses u,name n,": ",go t," = ",go x,"; ",go b]
      App _ f a       -> apps f a
      Typ _           -> "Type"
      All _ n u t b -> T.concat ["∀", alls n u t b]
      Slf _ n t       -> T.concat ["@",name n," ", go t]
      New _ t b       -> T.concat ["new ",go t, " ", go b]
      Eli _ t         -> T.concat ["use ",go t]
      Wrd _ w         -> T.pack (show w)
      Dbl _ d         -> T.pack (show d)
      I64 _           -> "i64"
      F64 _           -> "f64"
      Opr _ o a b     -> T.concat ["(", prettyPrim o, " ", go a, " ", go b, ")"]
      Ite _ c t f     -> T.concat ["if ", go c, " then ", go t, " else ", go f]

    lams :: Name -> Maybe (Uses, Term) -> Term -> Text
    lams n ut b = case b of
       Lam _ n' ut' b' -> T.concat [txt, lams n' ut' b']
       _               -> T.concat [txt, " => ", go b]
       where
         txt = case ut of
            Nothing    -> T.concat [" ", n]
            Just (u,t) -> T.concat [" (", uses u, n,": ", go t,")"]

    alls :: Name -> Uses -> Term -> Term -> Text
    alls n u t b = case b of
      All _ n' u' t' b' -> T.concat [txt, alls n' u' t' b']
      _                 -> T.concat [txt, " -> ", go b]
      where
        txt = case (n, u, t) of
          ("", Many, t) -> T.concat [" ", go t]
          _             -> T.concat [" (", uses u, n,": ", go t,")"]

    apps :: Term -> Term -> Text
    apps f@(Lam _ _ _ _) a  = T.concat ["(", go f, ") ", go a]
    apps f  a@(Lam _ _ _ _) = T.concat [go f, " (", go a, ")"]
    apps f (App _ af aa)    = T.concat [go f, " ", "(", apps af aa,")"]
    apps (App _ af aa) a    = T.concat [apps af aa, " ", go a]
    apps f a                = T.concat [go f, " ", go a]

instance Show Term where
  show t = T.unpack $ prettyTerm t

-- * Serialisation datatypes

-- | Terms with the source locations and names removed. We do this so the
-- serialisation only encodes relevant information (i.e. Names and Locs are just
-- metadata that don't affect typechecking or execution)
data Anon where
  VarA :: Int -> Anon
  RefA :: CID -> Anon
  LamA :: Maybe (Uses,Anon) -> Anon -> Anon
  LetA :: Uses -> Anon -> Anon -> Anon -> Anon
  AppA :: Anon -> Anon -> Anon
  TypA :: Anon
  AllA :: Uses -> Anon -> Anon -> Anon
  SlfA :: Anon -> Anon
  NewA :: Anon -> Anon -> Anon
  EliA :: Anon -> Anon
  WrdA :: Word64 -> Anon
  DblA :: Double -> Anon
  I64A :: Anon
  F64A :: Anon
  OprA :: Prim -> Anon -> Anon -> Anon
  IteA :: Anon -> Anon -> Anon -> Anon

-- | This encoding is designed to match the
-- [js-ipld-dag-cbor](https://github.com/ipld/js-ipld-dag-cbor) library's
-- encoding of the isomorphic JSON structure defined by:
--
-- > const Var = (indx)                => ({$0:"Var",$1:indx});
-- > const Ref = (cid)                 => ({$0:"Ref",$1:cid});
-- > const Lam = (uses,type, body)     => ({$0:"Lam",$1:uses,$2:type,$3:body});
-- > const Let = (uses,type,expr,body) => ({$0:"Let",$1:uses,$2:type,$3:expr,$4:body});
-- > const App = (func,argm)           => ({$0:"App",$1:func,$2:argm});
-- > const Typ = ()                    => ({$0:"Typ"})
-- > const I64 = ()                    => ({$0:"I64"})
-- > const F64 = ()                    => ({$0:"F64"})
-- > const Wrd = (word)                => ({$0:"Wrd",$1:word})
-- > const Dbl = (word)                => ({$0:"Dbl",$1:word})
-- > const Opr = (prim, argx, argy)    => ({$0:"Opr",$1:prim,$2:argx,$3:argy});
-- > const Ite = (cond, btru, bfls)    => ({$0:"Ite",$1:cond,$2:btru,$3:bfls});
-- > const All = ()                    => ({$0:"All",$1:uses,$2:type,$3:body});
-- > const Slf = (body)                => ({$0:"Slf",$1:body})
-- > const Eli = (body)                => ({$0:"Eli",$1:body})
-- > const New = (type, body)          => ({$0:"New",$1:type,$2:body})
encodeAnon :: Anon -> Encoding
encodeAnon term = case term of
  TypA                 -> encodeMapLen 1
                          <> (encodeString "$0" <> encodeString "Typ")
  I64A                 -> encodeMapLen 1
                          <> (encodeString "$0" <> encodeString "I64")
  F64A                 -> encodeMapLen 1
                          <> (encodeString "$0" <> encodeString "F64")
  VarA idx             -> encodeMapLen 2
                          <> (encodeString "$0" <> encodeString "Var")
                          <> (encodeString "$1" <> encodeInt idx)
  RefA cid             -> encodeMapLen 2
                          <> (encodeString "$0" <> encodeString "Ref")
                          <> (encodeString "$1" <> encodeCID     cid)
  SlfA trm             -> encodeMapLen 2
                          <> (encodeString "$0" <> encodeString "Slf")
                          <> (encodeString "$1" <> encodeAnon trm)
  EliA trm             -> encodeMapLen 2
                          <> (encodeString "$0" <> encodeString "Eli")
                          <> (encodeString "$1" <> encodeAnon trm)
  WrdA wrd             -> encodeMapLen 2
                          <> (encodeString "$0" <> encodeString "Wrd")
                          <> (encodeString "$1" <> encodeWord64 wrd)
  DblA dbl             -> encodeMapLen 2
                          <> (encodeString "$0" <> encodeString "Dbl")
                          <> (encodeString "$1" <> encodeDouble dbl)
  AppA fun arg         -> encodeMapLen 3
                          <> (encodeString "$0" <> encodeString "App")
                          <> (encodeString "$1" <> encodeAnon    fun)
                          <> (encodeString "$2" <> encodeAnon    arg)
  NewA typ trm         -> encodeMapLen 3
                          <> (encodeString "$0" <> encodeString "New")
                          <> (encodeString "$1" <> encodeAnon typ)
                          <> (encodeString "$2" <> encodeAnon trm)
  LamA typ bdy         -> encodeMapLen 3
                          <> (encodeString "$0" <> encodeString "Lam")
                          <> (encodeString "$1" <> encodeMaybeTyp typ)
                          <> (encodeString "$2" <> encodeAnon bdy)
  AllA use typ bdy     -> encodeMapLen 4
                          <> (encodeString "$0" <> encodeString "All")
                          <> (encodeString "$1" <> encodeInt (fromEnum use))
                          <> (encodeString "$2" <> encodeAnon typ)
                          <> (encodeString "$3" <> encodeAnon bdy)
  OprA opr arx ary     -> encodeMapLen 4
                          <> (encodeString "$0" <> encodeString "Opr")
                          <> (encodeString "$1" <> encodeInt (fromEnum opr))
                          <> (encodeString "$2" <> encodeAnon arx)
                          <> (encodeString "$3" <> encodeAnon ary)
  IteA cnd tru fls     -> encodeMapLen 4
                          <> (encodeString "$0" <> encodeString "Ite")
                          <> (encodeString "$1" <> encodeAnon cnd)
                          <> (encodeString "$2" <> encodeAnon tru)
                          <> (encodeString "$3" <> encodeAnon fls)
  LetA use typ exp bdy -> encodeMapLen 5
                          <> (encodeString "$0" <> encodeString "Let")
                          <> (encodeString "$1" <> encodeInt (fromEnum use))
                          <> (encodeString "$2" <> encodeAnon typ)
                          <> (encodeString "$3" <> encodeAnon exp)
                          <> (encodeString "$4" <> encodeAnon bdy)

encodeMaybeTyp :: Maybe (Uses,Anon) -> Encoding
encodeMaybeTyp Nothing      = encodeListLen 0
encodeMaybeTyp (Just (u,t)) = encodeListLen 2
                              <> encodeInt (fromEnum u)
                              <> encodeAnon t

-- | A helpful utility function like `when`, but with with pretty text errors
failM :: (Monad m, MonadFail m) => Bool -> [Text] -> m ()
failM c msg = if c then fail (T.unpack $ T.concat $ msg) else return ()

-- | A utility for erroring in a Decoder when we attempt to decode a field
decodeField :: Text -> Text -> Decoder s a -> Decoder s a
decodeField err nam decoder = do
  field <- decodeString
  failM (field /= nam)
    ["invalid ",err," field \"",field,"\"","expected \"",nam, "\"" ]
  decoder

-- | A utility for erroring in a Decoder when we attempt to decode a
-- constructor that matches one of a given set of names.
decodeCtor :: Text -> Text -> [Text] -> Decoder s Text
decodeCtor err field ns = do
  value <- decodeField err field decodeString
  failM (not $ value `elem` ns)
    ["invalid constructor tag at \"",field,"\""
    ,"expected one of: ",T.intercalate ", " ns
    ]
  return value

-- | `Uses` is an `Enum` instance, but we define a separate decoding function
-- for convenience.
decodeUses :: Decoder s Uses
decodeUses = toEnum <$> decodeInt

-- | `Prim` is an `Enum` instance, but we define a separate decoding function
-- for convenience.
decodePrim :: Decoder s Prim
decodePrim = toEnum <$> decodeInt

decodeMaybeTyp :: Decoder s (Maybe (Uses, Anon))
decodeMaybeTyp = do
  size <- decodeListLen
  case size of
    0 -> return Nothing
    2 -> do
      u <- decodeUses
      t <- decodeAnon
      return (Just (u,t))
    _ -> fail "invalid list size"

-- | Decode an `Encoding` generated by `encodeAnon`
decodeAnon :: Decoder s Anon
decodeAnon = do
  size <- decodeMapLen
  case size of
    1 -> do
      ctor <- decodeCtor "Anon" "$0" ["Typ", "I64", "F64"]
      case ctor of
        "Typ" -> return TypA
        "I64" -> return I64A
        "F64" -> return F64A
        _ -> fail $ "invalid ctor: " ++ T.unpack ctor
    2 -> do
      ctor <- decodeCtor "Anon" "$0" ["Var", "Ref", "Slf", "Eli", "Wrd", "Dbl"]
      case ctor of
        "Var" -> VarA <$> decodeField "Var" "$1" decodeInt
        "Ref" -> RefA <$> decodeField "Ref" "$1" decodeCID
        "Slf" -> SlfA <$> decodeField "Slf" "$1" decodeAnon
        "Eli" -> EliA <$> decodeField "Eli" "$1" decodeAnon
        "Wrd" -> WrdA <$> decodeField "Wrd" "$1" decodeWord64
        "Dbl" -> DblA <$> decodeField "Dbl" "$1" decodeDouble
    3 -> do
      ctor <- decodeCtor "Anon" "$0" ["App", "New", "Lam"]
      case ctor of
        "App" -> AppA <$> decodeField "App" "$1" decodeAnon
                      <*> decodeField "App" "$2" decodeAnon
        "New" -> NewA <$> decodeField "New" "$1" decodeAnon
                      <*> decodeField "New" "$2" decodeAnon
        "Lam" -> LamA <$> decodeField "Lam" "$1" decodeMaybeTyp
                      <*> decodeField "Lam" "$2" decodeAnon
    4 -> do
      ctor <- decodeCtor "Anon" "$0" ["All", "Opr", "Ite"]
      case ctor of
        "All" -> AllA <$> decodeField "All" "$1" decodeUses
                      <*> decodeField "All" "$2" decodeAnon
                      <*> decodeField "All" "$3" decodeAnon
        "Opr" -> OprA <$> decodeField "Opr" "$1" decodePrim
                      <*> decodeField "Opr" "$2" decodeAnon
                      <*> decodeField "Opr" "$3" decodeAnon
        "Ite" -> IteA <$> decodeField "Ite" "$1" decodeAnon
                      <*> decodeField "Ite" "$2" decodeAnon
                      <*> decodeField "Ite" "$3" decodeAnon
    5 -> do
      ctor <- decodeCtor "Anon" "$0" ["Let"]
      case ctor of
        "Let" -> LetA <$> decodeField "Let" "$1" decodeUses
                      <*> decodeField "Let" "$2" decodeAnon
                      <*> decodeField "Let" "$3" decodeAnon
                      <*> decodeField "Let" "$4" decodeAnon
    _ -> fail "invalid map size"

instance Serialise Anon where
  encode = encodeAnon
  decode = decodeAnon


--testTerm = LamA Many TypA (VarA 0)
--cid1 = anonCID testTerm
--testTerm2 = AppA testTerm (RefA cid1)


-- | This encoding is designed to match the
-- [js-ipld-dag-cbor](https://github.com/ipld/js-ipld-dag-cbor) library's
-- encoding of the isomorphic JSON structure defined by:
--
-- > const Loc = (from, upto) => ({$0:"Loc",$1:from,$2:upto})
--
-- where @from@ and @upto@ are integers.
encodeLoc :: Loc -> Encoding
encodeLoc (Loc from upto) = encodeMapLen 3
  <> (encodeString "$0" <> encodeString "Loc")
  <> (encodeString "$1" <> encodeInt from)
  <> (encodeString "$2" <> encodeInt upto)

-- | Decode an `Encoding` of a `Loc` generated by `encodeLoc`
decodeLoc :: Decoder s Loc
decodeLoc = do
  size <- decodeMapLen
  failM (size /= 3) ["invalid map size: ", T.pack $ show size]
  decodeCtor "Loc" "$0" ["Loc"]
  from <- decodeField "Loc" "$1" decodeInt
  upto <- decodeField "Loc" "$2" decodeInt
  return $ Loc from upto

instance Serialise Loc where
  encode = encodeLoc
  decode = decodeLoc

-- | Stores the `Name` and source layout `Loc` information from a `Term`
data Meta = Meta
  { _names :: IntMap Name
  , _locs  :: IntMap Loc
  } deriving (Show,Eq)

-- | This encoding is designed to match the
-- [js-ipld-dag-cbor](https://github.com/ipld/js-ipld-dag-cbor) library's
-- encoding of the isomorphic JSON structure defined by:
--
-- > const Meta = (nams, locs) => ({$0:"Meta", $1:nams, $2:locs})
--
-- where nams and locs are maps of integers to strings and `Loc`, using the
-- standard cborg map encoding.
encodeMeta :: Meta -> Encoding
encodeMeta (Meta ns ls) = encodeMapLen 3
    <> (encodeString "$0" <> encodeString "Meta")
    <> (encodeString "$1" <> encode ns)
    <> (encodeString "$2" <> encode ls)

-- | Decode an `Encoding` generate by `encodeMeta`
decodeMeta :: Decoder s Meta
decodeMeta = do
  size  <- decodeMapLen
  failM (size /= 3) ["invalid map size: ", T.pack $ show size]
  decodeCtor "Meta" "$0" ["Meta"]
  ns <- decodeField "Meta" "$1" decode
  ls <- decodeField "Meta" "$2" decode
  return $ Meta ns ls

instance Serialise Meta where
  encode = encodeMeta
  decode = decodeMeta

-- * Metadata Saturation and Desaturation

-- | Desaturate a term from its metadata. This works by assigning each node of
-- the term tree a number based on a left-to-right depth-first traversal. Note
-- that we must provide a top level `Name` and `Loc`. This is because
-- Yatima forbids the construction of open terms (terms with free variables).
-- Accordingly, an unbound variable is considered to be a recursive
-- self-reference (though only 1 free index is used for this). Another way to
-- conceptualize this is that `desaturate` should only be used on `Terms`
-- correctly parsed by the defintion parser in "Language.Yatima.Parse"
desaturate :: Name -> Loc -> Term -> (Anon,Meta)
desaturate n l t = let (a,(nm,_)) = runState (go t) (init,1) in (a,nm)
  where
    init = Meta (IM.singleton 0 n) (IM.singleton 0 l)

    bind :: Name -> State (Meta,Int) ()
    bind n = modify (\(Meta ns ls,i) -> (Meta (IM.insert i n ns) ls, i))

    locs :: Loc -> State (Meta,Int) ()
    locs n = modify (\(Meta ns ls,i) -> (Meta ns (IM.insert i l ls), i+1))

    go :: Term -> State (Meta,Int) Anon
    go t = case t of
      Typ l           -> locs l >> return TypA
      I64 l           -> locs l >> return I64A
      F64 l           -> locs l >> return F64A
      Wrd l w         -> locs l >> return (WrdA w)
      Dbl l d         -> locs l >> return (DblA d)
      Var l n idx     -> bind n >> locs l >> return (VarA idx)
      Ref l n hsh     -> bind n >> locs l >> return (RefA hsh)
      Slf l n t       -> bind n >> locs l >> SlfA <$> go t
      Eli l b         -> locs l >> EliA <$> go b
      Lam l n ut b    -> case ut of
        Just (u,t) -> bind n >> locs l >> LamA <$> (Just . (u,) <$> go t) <*> go b
        _          -> bind n >> locs l >> LamA Nothing <$> go b
      All l n u t b   -> bind n >> locs l >> AllA u <$> go t <*> go b
      Let l n u x t b -> bind n >> locs l >> LetA u <$> go x <*> go t <*> go b
      App l f a       -> locs l >> AppA <$> go f <*> go a
      New l t b       -> locs l >> NewA <$> go t <*> go b
      Opr l o a b     -> locs l >> OprA o <$> go a <*> go b
      Ite l c t f     -> locs l >> IteA <$> go c <*> go t <*> go f

-- TODO: Quickcheck the rename . uname  = id property

-- | Resaturate an anonymous term with its metadata. This function can't fail,
-- but there are no checks that `Meta` argument is not corrupt.
resaturate :: Anon -> Meta -> Term
resaturate anon meta = fst $ runState (go anon) (meta,1)
  where
    defName (Meta ns ls) = ns IM.! 0

    nameLoc :: State (Meta, Int) (Name, Loc)
    nameLoc = do
      (Meta ns ls,i) <- get
      let n = maybe "" id (IM.lookup i ns)
      let l = maybe noLoc id (IM.lookup i ls)
      put (Meta ns ls, i+1)
      return (n,l)

    go :: Anon -> State (Meta,Int) Term
    go t = case t of
      TypA         -> nameLoc >>= \(n,l) -> return $ Typ l
      I64A         -> nameLoc >>= \(n,l) -> return $ I64 l
      F64A         -> nameLoc >>= \(n,l) -> return $ F64 l
      WrdA w       -> nameLoc >>= \(n,l) -> return $ Wrd l w
      DblA d       -> nameLoc >>= \(n,l) -> return $ Dbl l d
      VarA idx     -> nameLoc >>= \(n,l) -> return $ Var l n idx
      LamA ut b    -> case ut of
        Just (u,t) -> nameLoc >>= \(n,l) -> Lam l n <$> (Just . (u,) <$> go t) <*> go b
        _          -> nameLoc >>= \(n,l) -> Lam l n Nothing <$> go b
      AllA u t b   -> nameLoc >>= \(n,l) -> All l n u <$> go t <*> go b
      LetA u x t b -> nameLoc >>= \(n,l) -> Let l n u <$> go x <*> go t <*> go b
      SlfA t       -> nameLoc >>= \(n,l) -> Slf l n <$> go t
      NewA t b     -> nameLoc >>= \(n,l) -> New l   <$> go t <*> go b
      EliA b       -> nameLoc >>= \(n,l) -> Eli l   <$> go b
      AppA f a     -> nameLoc >>= \(n,l) -> App l   <$> go f <*> go a
      OprA o a b   -> nameLoc >>= \(n,l) -> Opr l o <$> go a <*> go b
      IteA c t f   -> nameLoc >>= \(n,l) -> Ite l   <$> go c <*> go t <*> go f
      RefA cid     -> nameLoc >>= \(n,l) -> return $ Ref l n cid
