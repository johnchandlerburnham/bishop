{-# LANGUAGE OverloadedStrings #-}
module Language.Yatima.Parse where

import           Prelude                    hiding (all)

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.RWS.Lazy     hiding (All)

import           Data.Char                  (isSpace, isDigit)
import           Data.Map                   (Map)
import qualified Data.Map                   as M
import qualified Data.IntMap                as IM
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import qualified Data.Text.IO               as TIO
import           Data.Void
import           Data.Word

import           System.Exit

import           Text.Megaparsec            hiding (State, parseTest)
import           Text.Megaparsec.Char       hiding (space)
import qualified Text.Megaparsec.Char.Lexer as L

import           Codec.Serialise
import           Data.IPLD.CID              (CID)
import qualified Data.IPLD.CID              as CID

import           Language.Yatima.Term
import           Language.Yatima.Defs

-- | The environment of a Parser
data ParseEnv = ParseEnv
  { -- | The binding context for local variables
    _context :: [Name]
    -- | The set of global defintions, extended by definitions defined above in
    -- the current file. Yatima forbids mutual recursion, and currently requires
    -- references which point to definitions in the same file to be defined
    -- /after/ their referent in the file.
  , _defs    :: Defs
  }

-- | An empty parser environment, useful for testing
defaultParseEnv = ParseEnv [] (Defs M.empty M.empty)

-- | Custom parser errrors with bespoke messaging
data YatimaParseError
  = ConflictingParameterNames Name
  | ConflictingTypeDefName Name Name
  | UndefinedReference Name
  | UncachedCID Name CID
  | ReservedKeyword Name
  | LeadingDigit Name
  | LeadingApostrophe Name
  | I64Overflow Integer
  deriving (Eq, Ord, Show)

instance ShowErrorComponent YatimaParseError where
  showErrorComponent (ConflictingParameterNames nam) =
    "Conflicting definitions for: " ++ T.unpack nam ++ " in the same binder"
  showErrorComponent (ConflictingTypeDefName name ty_name) =
    "The name of definition " ++ T.unpack name ++
      " conflicts with the name of its type definition " ++ T.unpack ty_name
  showErrorComponent (UndefinedReference nam) =
    "Undefined reference: " ++ T.unpack nam
  showErrorComponent (UncachedCID nam cid ) =
    "Uncached content ID for: " ++ T.unpack nam ++ ", " ++ show cid
  showErrorComponent (ReservedKeyword nam) =
    "Reserved keyword: " ++ T.unpack nam
  showErrorComponent (LeadingDigit nam) = 
    "illegal leading digit in name: " ++ T.unpack nam
  showErrorComponent (LeadingApostrophe nam) =
    "illegal leading apostrophe in name: " ++ T.unpack nam
  showErrorComponent (I64Overflow w) =
    "i64 number is greater than 2^64: " ++ show w

-- | The type of the Yatima Parser
type Parser = RWST ParseEnv () () (ParsecT YatimaParseError Text Identity)

-- | A top level parser with default env and state
parseDefault :: Show a => Parser a -> Text
             -> Either (ParseErrorBundle Text YatimaParseError) a
parseDefault p s = do
  (a,_,_) <- runIdentity $ runParserT (runRWST p defaultParseEnv ()) "" s
  return a

-- | A useful testing function
parserTest :: Show a => Parser a -> Text -> IO ()
parserTest p s = Prelude.print $ parseDefault p s

-- | A utility for running a `Parser`, since the `RWST` monad wraps `ParsecT`
parse' :: Show a => Parser a -> ParseEnv -> String -> Text
       -> Either (ParseErrorBundle Text YatimaParseError) a
parse' p env file txt = do
  (a,_,_) <- runIdentity $ runParserT (runRWST p env ()) file txt
  return a

-- | Parser an alphanumeric name character which can include underscores and
-- apostrophes, but cannot begin with digits or apostrophes. Additionally,
-- Yatima reserves the keywords, @let@, @if@, @then@, @else@, @where@, @case@,
-- @new@, @elim@.
pName :: Parser Text
pName = label "a name: \"someFunc\",\"somFunc'\",\"x_15\", \"_1\"" $ do
  n  <- alphaNumChar <|> oneOf nameSymbol
  ns <- many (alphaNumChar <|> oneOf nameSymbol)
  let nam = T.pack (n : ns)
  if | isDigit n                -> customFailure $ LeadingDigit nam
     | n == '\''                -> customFailure $ LeadingApostrophe nam
     | nam `elem` reservedWords -> customFailure $ ReservedKeyword nam
     | otherwise -> return nam
  where
    nameSymbol = "_'" :: [Char]

    reservedWords :: [Text]
    reservedWords = ["module"
                    , "let"
                    , "if"
                    , "then"
                    , "else"
                    , "where"
                    , "case"
                    , "new"
                    , "elim"
                    ] ++ primNames

-- | A utility which checks if a character is a space and not a new line. This
-- is used to implement indentation sensitive parsing.
isSpaceNoNewLine :: Char -> Bool
isSpaceNoNewLine '\n' = False
isSpaceNoNewLine c    = isSpace c

-- | Consume non-newline whitespace
sc1 :: Parser ()
sc1 = void $ takeWhile1P (Just "white space without newlines") isSpaceNoNewLine

-- | Consume non-newline whitespace, while skipping comments. Yatima line
-- comments begin with @--@, and block comments are bracketed by @{-@ and @-}@
-- symbols.
space :: Parser ()
space = L.space sc1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

-- | Consume newline whitespace, while skipping comments. Yatima line comments
-- begin with @--@, and block comments are bracketed by @{-@ and @-}@ symbols.
spaceNL :: Parser ()
spaceNL = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

-- | A symbol is a string which can be followed by whitespace. The @sc@ argument
-- is for parsing indentation sensitive whitespace
symbol :: Parser () -> Text -> Parser Text
symbol sc txt = L.symbol sc txt

-- | Add a list of names to the binding context
bind :: [Name] -> Parser a -> Parser a
bind bs p = local (\e -> e { _context = (reverse bs) ++ _context e }) p

-- | Find a name in the binding context and return its index
find :: Name -> [Name] -> Maybe Int
find n cs = go n cs 0
  where
    go n (c:cs) i
      | n == c    = Just i
      | otherwise = go n cs (i+1)
    go _ [] _     = Nothing

-- | Parse a quantitative usage semirig annotation. The absence of annotation is
-- considered to be the `Many` multiplicity.
pUses :: Parser Uses
pUses = choice
  [ symbol space "0" >> return Zero
  , symbol space "1" >> return Once
  , return Many
  ]

-- | Parse the type of types: `Type`
pTyp :: Parser Term
pTyp = do
  from <- getOffset
  string "Type"
  upto <- getOffset
  return $ Typ (Loc from upto)

-- | Parse the type of @i64@ values: `I64`
pI64 :: Parser Term
pI64 = do
  from <- getOffset
  string "I64"
  upto <- getOffset
  return $ I64 (Loc from upto)

-- | Parse the type of @f64@ values: `F64`
pF64 :: Parser Term
pF64 = do
  from <- getOffset
  string "F64"
  upto <- getOffset
  return $ F64 (Loc from upto)

-- | Parse a lambda: @\0 x: A, 1 y : B, z : C => body@
pLam :: Parser () -> Parser Term
pLam sc = label "a lambda: \"\\0 x: A, 1 y : B, z : C => body" $ do
  from <- getOffset
  symbol sc "\\"
  bs   <- binds []
  body <- bind (snd3 <$> bs) (pExpr sc)
  upto <- getOffset
  return $ foldr (\(u,n,t) x -> Lam (Loc from upto) n u t x) body bs
  where
    snd3 (_,x,_) = x
    next :: [(Uses, Name, Term)] -> Parser [(Uses, Name, Term)]
    next bs = ((try $ sc >> symbol sc "=>") >> return (reverse bs))
                <|> ((sc >> symbol sc ",") >> binds bs)

    binds :: [(Uses, Name, Term)] -> Parser [(Uses, Name, Term)]
    binds bs = do
      use <- pUses <* sc
      nam <- pName <* sc
      symbol sc ":"
      typ <- bind (snd3 <$> bs) (pExpr sc)
      if nam `elem` (snd3 <$> bs)
      then customFailure $ ConflictingParameterNames nam
      else next ((use,nam,typ):bs)

-- | Parse a "forall" universal quantifier type: @(0 A: Type) -> (x : A) -> A@
pAll :: Parser () -> Parser Term
pAll sc = label "a forall: \"\\ (0 A: Type) -> (x : A) -> A\"" $ do
  from <- getOffset
  symbol sc "("
  use <- pUses
  nam <- pName <* space
  symbol sc ":"
  typ <- pExpr sc
  symbol sc ")"
  symbol sc "->"
  body <- bind [nam] (pExpr sc)
  upto <- getOffset
  return $ All (Loc from upto) nam use typ body

-- | Parse an unquantified function arrow: @A -> B@
pArr :: Parser () -> Parser Term
pArr sc = label "an arrow: \"\\ A -> B\"" $ do
  from <- getOffset
  uses <- pUses
  typ  <- pVar <* space
  symbol sc "->"
  body <- pExpr sc
  upto <- getOffset
  return $ All (Loc from upto) "" uses typ body

-- | Parse a self-type: @\@self body@
pSlf :: Parser () -> Parser Term
pSlf sc = do
  from <- getOffset
  string "@"
  n    <- pName
  sc
  body <- bind [n] (pExpr sc)
  upto <- getOffset
  return $ Slf (Loc from upto) n body

-- | Parse the declaration of a self-type value: 
-- @new Bool (\0 P: Bool -> Type, t: @self P(self), f: @self P(self) => t)
pNew :: Parser () -> Parser Term
pNew sc = do
  from <- getOffset
  symbol sc "new"
  typ_ <- pTerm sc
  body <- pTerm sc
  upto <- getOffset
  return $ New (Loc from upto) typ_ body

-- | Parse the elimination of a self type value: @elim True@
pEli :: Parser () -> Parser Term
pEli sc = do
  from <- getOffset
  symbol sc "elim"
  body <- pTerm sc
  upto <- getOffset
  return $ Eli (Loc from upto) body

-- | Parse a 64-bit word value
pWrd :: Parser Term
pWrd = do
  from <- getOffset
  w <- choice
    [ string "0x" >> L.hexadecimal
    , string "0b" >> L.binary
    , L.decimal
    ]
  upto <- getOffset
  if (w :: Integer) >= 2^64
  then customFailure $ I64Overflow w
  else return $ Wrd (Loc from upto) (fromIntegral w)

-- | Parse a double-width floating point value
pDbl :: Parser Term
pDbl = do
  from <- getOffset
  f    <- L.float <|> L.signed (pure ()) L.float
  upto <- getOffset
  return $ Dbl (Loc from upto) f

-- | Parse a numeric if-then-else
pIte :: Parser () -> Parser Term
pIte sc = do
  from <- getOffset
  symbol sc "if"
  c <- pExpr sc
  symbol sc "then"
  t <- pExpr sc
  symbol sc "else"
  f <- pExpr sc
  upto <- getOffset
  return $ Ite (Loc from upto) c t f

-- | Parse a `Prim` type defined in "Language.Yatima.Prim"
pPrim :: Parser Prim
pPrim = choice $ zipWith (\x y -> string x >> return (toEnum y)) primNames [0..]

-- | Parse a primitive numeric operation
pOpr :: Parser () -> Parser Term
pOpr sc = do
  from <- getOffset
  string "#"
  p <- pPrim <* sc
  a <- pTerm sc
  b <- pTerm sc
  upto <- getOffset
  return $ Opr (Loc from upto) p a b

-- | Parse a local variable or a locally indexed alias of a global reference
pVar :: Parser Term
pVar = label "a local or global reference: \"x\", \"add\"" $ do
  from <- getOffset
  ctx <- asks _context
  nam <- pName
  upto <- getOffset
  case find nam ctx of
    Just i  -> return $ Var (Loc from upto) nam i
    Nothing -> do
      Defs index cache <- asks _defs
      case M.lookup nam index of
        Nothing  -> customFailure $ UndefinedReference nam
        Just cid -> return $ Ref (Loc from upto) nam cid

-- | Parse a Yatima `Term`, with an expression (an sequence of term
-- applications) must be guarded by parentheses
pTerm :: Parser () -> Parser Term
pTerm sc = do
  choice
    [ pTyp
    , pI64
    , pF64
    , try $ pDbl
    , pWrd
    , pSlf sc
    , pNew sc
    , pEli sc
    , pOpr sc
    , pIte sc
    , try $ pAll sc
    , symbol sc "(" >> pExpr sc <* string ")"
    , pLam sc
    , try $ pArr sc
    , pVar
    ]

-- | Parse a sequence of applied Yatima terms, with left-handed associativity
pExpr :: Parser () -> Parser Term
pExpr sc = label "an pExpression: \"f x y z\"" $ do
  from <- getOffset
  fun  <- pTerm sc
  optional $ try sc
  args <- try $ sepEndBy (pTerm sc) (try sc)
  upto <- getOffset
  return $ foldl (\t a -> App (Loc from upto) t a) fun args

-- | UNIMPLEMENTED STUB: Parse a documentation comment on a definition
pDefComment :: Parser Text
pDefComment = return "test"

-- | Parse the type of a definition
pDefType :: Parser (Loc, Name, Term)
pDefType = L.nonIndented (spaceNL) $ L.lineFold spaceNL $ \sc -> do
  from   <- getOffset
  nam    <- pName
  sc >> symbol sc ":"
  body   <- pExpr sc
  upto   <- getOffset
  return (Loc from upto, nam, body)

-- | Parse parameter on a definition
pParams :: Parser () -> [Name] -> Parser [Name]
pParams sc bs = choice
  [ (try $ (sc >> symbol sc "=")) >> return (reverse bs)
  , do
      nam <- sc >> pName
      when (nam `elem` bs) (customFailure $ ConflictingParameterNames nam)
      pParams sc (nam:bs)
  ]

-- | Parse a definition
pDef :: Parser DefDeref
pDef = label "a definition" $ do
  comment           <- pDefComment
  (typeLoc, typeName, typ_) <- pDefType
  L.nonIndented (spaceNL) $ L.lineFold spaceNL $ \sc -> do
    from   <- getOffset
    nam    <- pName
    when (nam /= typeName) (customFailure $ ConflictingTypeDefName nam typeName)
--    params <- maybe [] id <$> (optional $ space >> params sc [])
    sc >> symbol sc "="
    body   <- bind [nam] (pExpr sc)
    upto   <- getOffset
    let loc = Loc from upto
    --let (anon, meta) = unname nam loc (foldr (\n x -> Lam loc Many n (Typ loc) x) body params)
    let (termAnon, termMeta) = desaturate nam loc body
    let (typeAnon, typeMeta) = desaturate typeName typeLoc typ_
    return $ DefDeref comment termAnon termMeta typeAnon typeMeta

-- | Parse a sequence of definitions, e.g. in a file
pDefs :: Parser Defs
pDefs = (try end) <|> next
  where
  end = spaceNL >> eof >> asks _defs
  next = do
    ds@(Defs index cache) <- asks _defs
    DefDeref comm termAnon termMeta typeAnon typeMeta <- pDef
    let defName = (_names termMeta) IM.! 0
    let docCID     = makeCID comm
    let termAnonCID = makeCID termAnon :: CID
    let termMetaCID = makeCID termMeta :: CID
    let typeAnonCID = makeCID typeAnon :: CID
    let typeMetaCID = makeCID typeMeta :: CID
    let def         = Def docCID termAnonCID termMetaCID typeAnonCID typeMetaCID
    let defCID      = makeCID def
    let index'      = M.insert defName defCID index
    let cache'      = M.insert defCID      (serialise def)  $
                      M.insert typeAnonCID (serialise typeAnon) $
                      M.insert typeMetaCID (serialise typeMeta) $
                      M.insert termAnonCID (serialise termAnon) $
                      M.insert termMetaCID (serialise termMeta) $
                      M.insert docCID      (serialise comm) $
                      cache
    local (\e -> e { _defs = Defs index' cache' }) pDefs

-- | Parse a file
pFile :: FilePath -> IO Defs
pFile file = do
  txt <- TIO.readFile file
  case parse' pDefs (ParseEnv [] (Defs M.empty M.empty)) file txt of
    Left  e -> putStr (errorBundlePretty e) >> exitFailure
    Right m -> return m

-- | Parse and prettyprint a file
prettyFile :: FilePath -> IO ()
prettyFile file = do
  txt <- TIO.readFile file
  case parse' pDefs (ParseEnv [] (Defs M.empty M.empty)) file txt of
    Left  e -> putStr (errorBundlePretty e) >> exitFailure
    Right m -> putStrLn $ T.unpack $ prettyDefs m

