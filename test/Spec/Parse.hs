{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module Spec.Parse where

import           Prelude                    hiding (log)

import           Control.Monad.Identity
import           Control.Monad.RWS.Lazy     hiding (All)
import           Control.Monad.State.Strict

import           Data.List.NonEmpty         (NonEmpty)
import           Data.List.NonEmpty         as NE
import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as M
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import           Data.Void

import           Test.Hspec

import           Text.Megaparsec            hiding (State, parse)
import           Text.Megaparsec.Char       hiding (space)
import qualified Text.Megaparsec.Char.Lexer as L
import           Text.RawString.QQ

import           Codec.Serialise
import           Language.Bishop.Parse
import           Language.Bishop.Term

data Result a
  = Good a
  | Bad Int (Set (ErrorFancy BishopParseError))
  | Ugly (ParseErrorBundle Text BishopParseError)
  deriving (Eq, Show)

parse :: Parser a -> Text -> Result a
parse p txt =
  case runIdentity $ runParserT (runRWST p defaultParseEnv ()) "" txt of
    (Left  e)       -> case bundleErrors e of
      (FancyError pos es) NE.:| _  -> Bad pos es
      _                            -> Ugly e
    (Right (a,_,_)) -> Good a

mkBad :: Int -> BishopParseError -> Result a
mkBad pos e = Bad pos (Set.singleton (ErrorCustom e))

spec :: SpecWith ()
spec = do
  describe "Names" $ do
    it "alphanumeric plus underscore and apostrophe: \"a\"" $ do
      parse name "a" `shouldBe` (Good "a")
      parse name "a1" `shouldBe` (Good "a1")
      parse name "a'" `shouldBe` (Good "a'")
      parse name "a_" `shouldBe` (Good "a_")
    it "Error correctly on leading digit: \"1a\"" $ do
      parse name "1" `shouldBe` (mkBad 1 $ LeadingDigit "1")
    it "Error correctly on leading apostrophe: \"'a\"" $ do
      parse name "'a" `shouldBe` (mkBad 2 $ LeadingApostrophe "'a")
    it "Error correctly on reserved word: \"_\"" $ do
      parse name "_" `shouldBe` (mkBad 1 $ ReservedKeyword "_")

  describe "Lambda" $ do
    it "basic syntax: \"|x| x\"" $ do
      parse (lam space) "|x| x" `shouldBe` (Good $ Lam "x" $ Var "x" 0)
      parse (lam space) "|x| |y| x" `shouldBe` (Good $ Lam "x" $ Lam "y" $ Var "x" 1)
    it "multiple parameter syntax sugar: \"|x,y| x\"" $ do
      parse (lam space) "|x,y| x" `shouldBe` (Good $ Lam "x" $ Lam "y" $ Var "x" 1)

  describe "Definitions" $ do
    it "basic syntax: \"foo x = x\"" $ do
      parse def "foo x = x" `shouldBe` 
        (Good $ unname "foo" (Lam "x" (Var "x" 0)))
    it "self-reference: \"loop = loop\"" $ do
      parse def "loop = loop" `shouldBe` 
        (Good $ unname "loop" (Var "loop" 0))

    it "definitions: " $ do
      let txt = [r|
id x = x
 |]
      let (anon, meta) = unname "id" (Lam "x" (Var "x" 0))
      let def = Def (makeCID anon) (makeCID meta)
      --let bar_def        = Def (makeCID $ serialise bar_anon) (makeCID $ serialise bar_meta)
      parse defs txt `shouldBe` 
        (Good $ Defs
          (M.fromList
            [ ("id", makeCID $ def)
            ])
          (M.fromList
            [ (makeCID def, serialise def)
            , (makeCID anon, serialise anon)
            , (makeCID meta, serialise meta)
            ]))

    it "multiple definitions: " $ do
      let txt = [r|
foo x = (x x)
bar x = x
 |]
      let (foo_anon, foo_meta) = unname "foo" (Lam "x" (App (Var "x" 0) (Var "x" 0)))
      let (bar_anon, bar_meta) = unname "bar" (Lam "x" (Var "x" 0))
      let foo_def        = Def (makeCID foo_anon) (makeCID $ foo_meta)
      let bar_def        = Def (makeCID bar_anon) (makeCID $ bar_meta)
      parse defs txt `shouldBe` 
        (Good $ Defs
          (M.fromList
            [ ("foo", makeCID foo_def)
            , ("bar", makeCID bar_def)
            ])
          (M.fromList
            [ (makeCID foo_anon, serialise foo_anon)
            , (makeCID bar_anon, serialise bar_anon)
            , (makeCID foo_meta, serialise foo_meta)
            , (makeCID bar_meta, serialise bar_meta)
            , (makeCID foo_def, serialise foo_def)
            , (makeCID bar_def, serialise bar_def)
            ]))

      let txt = [r|
foo x = (x
  x)
bar x
  = x
|]
      let (foo_anon, foo_meta) = unname "foo" (Lam "x" (App (Var "x" 0) (Var "x" 0)))
      let (bar_anon, bar_meta) = unname "bar" (Lam "x" (Var "x" 0))
      let foo_def        = Def (makeCID foo_anon) (makeCID $ foo_meta)
      let bar_def        = Def (makeCID bar_anon) (makeCID $ bar_meta)
      parse defs txt `shouldBe` 
        (Good $ Defs
          (M.fromList
            [ ("foo", makeCID foo_def)
            , ("bar", makeCID bar_def)
            ])
          (M.fromList
            [ (makeCID foo_anon, serialise foo_anon)
            , (makeCID bar_anon, serialise bar_anon)
            , (makeCID foo_meta, serialise foo_meta)
            , (makeCID bar_meta, serialise bar_meta)
            , (makeCID foo_def, serialise foo_def)
            , (makeCID bar_def, serialise bar_def)
            ]))
