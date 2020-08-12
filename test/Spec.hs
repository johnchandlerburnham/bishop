module Main where

import           Test.Hspec
import           Test.QuickCheck

import           Spec.Parse as Parse

main :: IO ()
main = hspec $ do
  describe "Language.Bishop.Parse" $ Parse.spec
