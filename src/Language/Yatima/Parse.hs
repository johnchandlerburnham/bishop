{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections  #-}
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

import           Text.Megaparsec            hiding (State)
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
  = UndefinedReference Name
  | UncachedCID Name CID
  | ReservedKeyword Name
  | LeadingDigit Name
  | LeadingApostrophe Name
  | I64Overflow Integer
  deriving (Eq, Ord, Show)

instance ShowErrorComponent YatimaParseError where
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
parserTest p s = case parseDefault p s of
  Left  e -> putStr (errorBundlePretty e)
  Right x -> print x

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
                    , "forall"
                    , "lambda"
                    ] ++ primNames

-- | Consume whitespace, while skipping comments. Yatima line comments begin
-- with @//@, and block comments are bracketed by @*/@ and @*/@ symbols.
space :: Parser ()
space = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "/*" "*/")

-- | A symbol is a string which can be followed by whitespace. The @sc@ argument
-- is for parsing indentation sensitive whitespace
symbol :: Text -> Parser Text
symbol txt = L.symbol space txt

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
pUses ::  Parser Uses
pUses = pUsesAnnotation <|> return Many

pUsesAnnotation :: Parser Uses
pUsesAnnotation = choice
  [ symbol "0"       >> return Zero
  , symbol "1"       >> return Once
  ]

-- | Parse the type of types: `Type`
pTyp :: Int -> Parser Term
pTyp from = do
  string "Type"
  upto <- getOffset
  return $ Typ (Loc from upto)

-- | Parse the type of `I64` values
pI64 :: Int -> Parser Term
pI64 from = do
  string "I64"
  upto <- getOffset
  return $ I64 (Loc from upto)

-- | Parse the type of `F64` values
pF64 :: Int -> Parser Term
pF64 from = do
  string "F64"
  upto <- getOffset
  return $ F64 (Loc from upto)

fst3 :: (a,b,c) -> a
fst3 (x,y,z) = x


foldAll :: Loc -> Term -> [(Name, Maybe (Uses, Term))] -> Term
foldAll loc body bs = foldr (\(n,Just (u,t)) x -> All loc n u t x) body bs

foldLam:: Loc -> Term -> [(Name, Maybe (Uses, Term))] -> Term
foldLam loc body bs = foldr (\(n,ut) x -> Lam loc n ut x) body bs

-- | Parse a forall: @(0 A: Type, 1 x : A, z : C) -> body@ or
-- | parse a lambda: @(0 A: Type, 1 x : A, z : C) => body@
pLam :: Int -> Parser Term
pLam from = do
  from <- getOffset
  symbol "λ" <|> symbol "lambda"
  bs   <- pBinders True <* space
  symbol "=>"
  body <- bind (fst <$> bs) (pExpr False)
  upto <- getOffset
  let loc = Loc from upto
  return $ foldLam loc body bs

pAll :: Int -> Parser Term
pAll from = do
  from <- getOffset
  symbol "∀" <|> symbol "forall"
  bs   <- pBinders False <* space
  symbol "->"
  body <- bind (fst <$> bs) (pExpr False)
  upto <- getOffset
  let loc = Loc from upto
  return $ foldAll loc body bs

pBinder :: Bool -> Parser [(Name, Maybe (Uses, Term))]
pBinder annOptional  = if annOptional then ann <|> unAnn else ann
  where
    unAnn = pure . (,Nothing) <$> pName
    ann = do
      symbol "("
      uses  <- pUses
      names <- sepBy1 pName space
      typ_  <- symbol ":" >> pExpr False
      string ")"
      return $ (,Just (uses,typ_)) <$> names

-- | Parse a binding sequence @(0 A: Type) (1 x : A) (z : C)@
pBinders :: Bool -> Parser [(Name, Maybe (Uses, Term))]
pBinders annOpt = (try $ next) <|> (pBinder annOpt)
  where
   next = do
     b  <- pBinder annOpt <* space
     bs <- bind (fst <$> b) $ pBinders annOpt
     return $ b ++ bs

-- | Parse a self-type: @\@self body@
pSlf :: Int -> Parser Term
pSlf from = do
  string "@"
  n    <- pName <* space
  body <- bind [n] (pExpr False)
  upto <- getOffset
  return $ Slf (Loc from upto) n body

-- | Parse the declaration of a self-type value: 
-- @new Bool (\0 P: Bool -> Type, t: @self P(self), f: @self P(self) => t)
pNew :: Int -> Parser Term
pNew from = do
  symbol "new"
  typ_ <- pTerm
  body <- pExpr False
  upto <- getOffset
  return $ New (Loc from upto) typ_ body

-- | Parse the elimination of a self type value: @elim True@
pEli :: Int -> Parser Term
pEli from = do
  symbol "elim"
  body <- pExpr False
  upto <- getOffset
  return $ Eli (Loc from upto) body

-- | Parse a 64-bit word value
pWrd :: Int -> Parser Term
pWrd from = do
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
pDbl :: Int -> Parser Term
pDbl from = do
  f    <- L.float <|> L.signed (pure ()) L.float
  upto <- getOffset
  return $ Dbl (Loc from upto) f

-- | Parse a numeric if-then-else
pIte :: Int -> Parser Term
pIte from = do
  symbol "if"
  c <- pTerm
  symbol "then"
  t <- pTerm
  symbol "else"
  f <- pTerm
  upto <- getOffset
  return $ Ite (Loc from upto) c t f
--
-- | Parse a `Prim` numeric operation defined in "Language.Yatima.Prim"
pPrim :: Parser Prim
pPrim = choice $ zipWith (\x y -> string x >> return (toEnum y)) primNames [0..]

-- | Parse a primitive numeric operation
pOpr :: Int -> Parser Term
pOpr from = do
  string "#"
  p <- pPrim <* space
  a <- pTerm <* space
  b <- pTerm
  upto <- getOffset
  return $ Opr (Loc from upto) p a b

pDecl :: Int -> Parser (Name, Term, Term)
pDecl from = do
  nam <- pName <* space
  bs   <- pBinders False <* space
  typBody <- symbol ":" >> bind (fst <$> bs) (pExpr False)
  typUpto <- getOffset
  let typ = foldAll (Loc from typUpto) typBody bs
  symbol "="
  expBody <- bind (nam:(fst <$> bs)) $ pExpr False
  expUpto <- getOffset
  let exp = foldLam (Loc from expUpto) expBody bs
  return (nam, typ, exp)


-- | Parse a local, possibly recursive, definition
pLet :: Int -> Parser Term
pLet from = do
  symbol "let"
  use  <- pUses
  (nam,typ,exp) <- pDecl from
  symbol ";"
  bdy <- bind [nam] $ pExpr False
  upto <- getOffset
  return $ Let (Loc from upto) nam use typ exp bdy

-- | Parse a local variable or a locally indexed alias of a global reference
pVar :: Int -> Parser Term
pVar from = label "a local or global reference: \"x\", \"add\"" $ do
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

-- | Parse a Yatima `Term`
pTerm :: Parser Term
pTerm = do
  from <- getOffset
  t <- choice
    [ pTyp from
    , pI64 from
    , pF64 from
    , (try $ pDbl from) <|> (pWrd from)
    , pSlf from
    , pNew from
    , pEli from
    , pOpr from
    , pIte from
    , pLet from
    , pLam from
    , pAll from
    , pExpr True
    , pVar from
    ]
  choice
    [ --try $ pArr from t
    --, 
    return t
    ]

-- | Parse an unquantified function arrow: @A -> B@
pArr :: Int -> Term -> Parser Term
pArr from typ = label "an arrow: \"\\ A -> B\"" $ do
  space
  symbol "->"
  body <- pExpr False
  upto <- getOffset
  return $ All (Loc from upto) "" Many typ body

-- | Parse an application expression of Yatima terms, left-hand associative
pExpr :: Bool -> Parser Term
pExpr parens = do
  from <- getOffset
  when parens (void $ symbol "(")
  fun  <- pTerm <* space
  args <- sepEndBy pTerm space
  when parens (void $ string ")")
  upto <- getOffset
  return $ foldl (\t a -> App (Loc from upto) t a) fun args

---- | UNIMPLEMENTED STUB: Parse a documentation comment on a definition
pDefComment :: Parser Text
pDefComment = return "text"
--do
--  commLines <- many (string ">" (Just "comment character") (/= "\n")

-- | Parse a definition
pDef :: Parser DefDeref
pDef = label "a definition" $ do
  from    <- getOffset
  comment <- pDefComment
  symbol "def"
  (nam, typ, exp) <- pDecl from
  upto   <- getOffset
  let loc = Loc from upto
  let (termAnon, termMeta) = desaturate nam loc exp
  let (typeAnon, typeMeta) = desaturate nam loc typ
  return $ DefDeref comment termAnon termMeta typeAnon typeMeta

-- | Parse a sequence of definitions, e.g. in a file
pDefs :: Parser Defs
pDefs = (try $ space >> next) <|> end
  where
  end = space >> eof >> asks _defs
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

-- | Parse and pretty-print a file
prettyFile :: FilePath -> IO ()
prettyFile file = do
  txt <- TIO.readFile file
  case parse' pDefs (ParseEnv [] (Defs M.empty M.empty)) file txt of
    Left  e -> putStr (errorBundlePretty e) >> exitFailure
    Right m -> putStrLn $ T.unpack $ prettyDefs m

