{-# LANGUAGE OverloadedStrings #-}
module Language.Bishop.Parse where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.RWS.Lazy
import           Control.Monad.RWS.Lazy

import           Data.Char                  (isSpace, isDigit)
import           Data.Map                   (Map)
import qualified Data.Map                   as M
import qualified Data.IntMap                as IM
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import qualified Data.Text.IO               as TIO
import           Data.Void

import           System.Exit

import           Text.Megaparsec            hiding (State, parseTest)
import           Text.Megaparsec.Char       hiding (space)
import qualified Text.Megaparsec.Char.Lexer as L

import           Codec.Serialise
import           Data.IPLD.CID              (CID)
import qualified Data.IPLD.CID              as CID
import           Language.Bishop.Term

data ParseEnv = ParseEnv
  { _context :: [Name]
  , _defs    :: Defs
  }

data BishopParseError
  = ConflictingDefinitions Name
  | UndefinedReference Name
  | UncachedCID Name CID
  | ReservedKeyword Name
  | LeadingDigit Name
  | LeadingApostrophe Name
  deriving (Eq, Ord, Show)

instance ShowErrorComponent BishopParseError where
  showErrorComponent (ConflictingDefinitions nam) =
    "Conflicting definitions for: " ++ T.unpack nam ++ " in the same binder"
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

type Parser = RWST ParseEnv () () (ParsecT BishopParseError Text Identity)

defaultParseEnv = ParseEnv [] (Defs M.empty M.empty)

-- top level parser with default env and state
parseDefault :: Show a => Parser a -> Text
             -> Either (ParseErrorBundle Text BishopParseError) a
parseDefault p s = do
  (a,_,_) <- runIdentity $ runParserT (runRWST p defaultParseEnv ()) "" s
  return a

-- a useful testing function
parserTest :: Show a => Parser a -> Text -> IO ()
parserTest p s = Prelude.print $ parseDefault p s

parse' :: Show a => Parser a -> ParseEnv -> String -> Text
       -> Either (ParseErrorBundle Text BishopParseError) a
parse' p env file txt = do
  (a,_,_) <- runIdentity $ runParserT (runRWST p env ()) file txt
  return a

name :: Parser Text
name = label "a name: \"someFunc\",\"somFunc'\",\"x_15\", \"_1\"" $ do
  n  <- alphaNumChar <|> oneOf nameSymbol
  ns <- many (alphaNumChar <|> oneOf nameSymbol)
  let nam = T.pack (n : ns)
  if | isDigit n                -> customFailure $ LeadingDigit nam
     | n == '\''                -> customFailure $ LeadingApostrophe nam
     | nam `elem` reservedWords -> customFailure $ ReservedKeyword nam
     | otherwise -> return nam
  where
    nameSymbol = "_'" :: [Char]
    reservedWords = ["module", "let",  "where", "case", "_"] :: [Text]

isSpaceNoNewLine :: Char -> Bool
isSpaceNoNewLine '\n' = False
isSpaceNoNewLine c    = isSpace c

sc1 :: Parser ()
sc1 = void $ takeWhile1P (Just "white space without newlines") isSpaceNoNewLine

space :: Parser ()
space = L.space sc1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

spaceNL :: Parser ()
spaceNL = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

symbol :: Parser () -> Text -> Parser Text
symbol sc txt = L.symbol sc txt

bind :: [Name] -> Parser a -> Parser a
bind bs p = local (\e -> e { _context = (reverse bs) ++ _context e }) p

binders :: Parser sep -> Parser end -> [Name] -> Parser [Name]
binders sep end bs = (try $ end >> return (reverse bs)) <|> (sep >> next bs)
  where
    next bs = do
      nam <- name
      case nam `elem` bs of
        False -> binders sep end (nam:bs)
        True  -> customFailure $ ConflictingDefinitions nam

find :: Name -> [Name] -> Maybe Integer
find n cs = go n cs 0
  where
    go n (c:cs) i
      | n == c    = Just i
      | otherwise = go n cs (i+1)
    go _ [] _     = Nothing

lam :: Parser () -> Parser Term
lam sc = label "a lambda: \"|x,y,z| body\"" $ do
  symbol sc "|"
  bs <- name >>= (\b -> binders (symbol sc ",") (symbol sc "|") [b])
  body <- bind bs (expr sc)
  return $ foldr (\n x -> Lam n x) body bs

var :: Parser Term
var = label "a local or global reference: \"x\", \"add\"" $ do
  ctx <- asks _context
  nam <- name 
  case find nam ctx of
    Just i  -> return $ Var nam i
    Nothing -> do
      Defs index cache <- asks _defs
      case M.lookup nam index of
        Nothing  -> customFailure $ UndefinedReference nam
        Just cid -> case M.lookup cid cache of
          Nothing  -> customFailure $ UndefinedReference nam
          Just _   -> return $ Ref nam cid

term :: Parser () -> Parser Term
term sc = do
  choice
    [ symbol sc "(" >> expr sc <* string ")"
    , var
    , lam sc
    ]

expr :: Parser () -> Parser Term
expr sc = label "an expression: \"f x y z\"" $ do
  fun  <- term sc
  optional $ try sc
  args <- sepEndBy (term sc) (try sc)
  return $ foldl (\t a -> App t a) fun args

def :: Parser (Anon,Meta)
def = label "a definition: \"foo x y z = z\"" $ 
  L.nonIndented (spaceNL) $ 
  L.lineFold spaceNL $ \sc -> do
    nam    <- name <* space
    params <- maybe [] id <$>
      (optional $ space >> binders sc (sc >> symbol sc "=") [])
    body   <- bind (nam:params) (expr sc)
    return $ unname nam (foldr (\n x -> Lam n x) body params)

defs :: Parser Defs
defs = (try end) <|> next
  where
  end = spaceNL >> eof >> asks _defs
  next = do
    ds@(Defs index cache) <- asks _defs
    (anon,meta) <- def
    let defName = (_names meta) IM.! 0
    let anonCID = makeCID anon :: CID
    let metaCID = makeCID meta :: CID
    let def     = Def anonCID metaCID
    let defCID  = makeCID def
    let index'  = M.insert defName defCID index
    let cache'  = M.insert defCID (serialise def) $
                  M.insert anonCID (serialise anon) $
                  M.insert metaCID (serialise meta) $
                  cache
    local (\e -> e { _defs = Defs index' cache' }) defs

parseFile :: FilePath -> IO Defs
parseFile file = do
  txt <- TIO.readFile file
  case parse' defs (ParseEnv [] (Defs M.empty M.empty)) file txt of
    Left  e -> putStr (errorBundlePretty e) >> exitFailure
    Right m -> return m

prettyFile :: FilePath -> IO ()
prettyFile file = do
  txt <- TIO.readFile file
  case parse' defs (ParseEnv [] (Defs M.empty M.empty)) file txt of
    Left  e -> putStr (errorBundlePretty e) >> exitFailure
    Right m -> putStrLn $ T.unpack $ prettyDefs m

