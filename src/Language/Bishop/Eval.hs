{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE MultiWayIf #-}
module Language.Bishop.Eval where

import           Control.Monad.ST
import           Control.Monad.ST.UnsafePerform

import           Data.Map                       (Map)
import qualified Data.Map                       as M
import           Data.Set                       (Set)
import qualified Data.Set                       as Set
import           Data.STRef
import           Data.Text                      (Text)
import qualified Data.Text                      as T
import qualified Data.Text.IO                   as TIO
import           Text.Megaparsec                (errorBundlePretty)

import qualified Data.ByteString.Lazy       as BSL

import           Data.IPLD.CID

import           System.Exit

import           Codec.Serialise

import           Language.Bishop.Term
import           Language.Bishop.Parse

data HOAS where
  VarH :: Name -> Integer -> HOAS
  LamH :: Name -> (HOAS -> HOAS) -> HOAS
  AppH :: HOAS -> HOAS -> HOAS
  RefH :: Name -> CID -> HOAS
  FixH :: Name -> (HOAS -> HOAS) -> HOAS

findCtx :: Integer -> [HOAS] -> Maybe HOAS
findCtx i cs = go cs 0
  where
    go (c:cs) j
      | i == j   = Just c
      | otherwise = go cs (j+1)
    go [] _     = Nothing

toHOAS :: Term -> [HOAS] -> Integer -> HOAS
toHOAS t ctx dep = let go = toHOAS in case t of
  Var n i -> case findCtx i ctx of
    Just trm -> trm
    Nothing  -> VarH n (dep - i - 1)
  Ref n h -> RefH n h
  App f a -> AppH (go f ctx dep) (go a ctx dep)
  Lam n b -> LamH n (\x -> (go b (x:ctx) (dep + 1)))

fromHOAS :: HOAS -> Integer -> Term
fromHOAS t dep = let go = fromHOAS in case t of
  FixH n b -> go (b (FixH n b)) dep
  VarH n i -> Var n (dep - i - 1)
  RefH n h -> Ref n h
  LamH n b -> Lam n (go (b (VarH n dep)) (dep + 1))
  AppH f a -> App (go f dep) (go a dep)

printHOAS :: HOAS -> Text
printHOAS = prettyTerm . (\x -> fromHOAS x 0)

data DefH = DefH { _name :: Name, _term :: HOAS}

toDefH :: Def -> Defs -> Maybe DefH
toDefH def ds = do
  trm <- getTerm def ds
  nam <- getName def ds
  return $ DefH nam (FixH nam (\s -> toHOAS trm [s] 1))

reduce :: HOAS -> Defs -> HOAS
reduce t ds = let go = \x -> reduce x ds in case t of
  FixH n b -> go (b (FixH n b))
  VarH n i -> VarH n i
  RefH n c -> case deref c ds of
    Just t  -> go $ FixH n (\s -> toHOAS t [s] 1)
    Nothing -> error "BAD: Undefined Reference during reduction"
  LamH n b -> LamH n b
  AppH f a -> case go f of
    LamH n b  -> go (b a)
    x         -> AppH f a

reduceName :: Name -> Defs -> Maybe Term
reduceName name ds = do
  def             <- indexLookup name ds
  (DefH nam term) <- toDefH def ds
  return $ (flip fromHOAS 1) $ reduce term ds

compText :: HOAS -> Integer -> Text
compText term dep = let go = compText in case term of
  VarH n x -> if x < 0
              then T.concat ["^", T.pack $ show $ dep + x]
              else T.concat ["#", T.pack $ show x]
  RefH n h -> T.concat ["&", n] 
  FixH _ b -> T.concat ["μ", go (b (VarH "" (0-dep-1))) (dep+1)]
  LamH n b -> T.concat ["λ", go (b (VarH "" (0-dep-1))) (dep+1)]
  AppH f a -> T.concat ["@", go f dep, go a dep]

normalize :: DefH -> Defs -> Term
normalize dh defs = (flip fromHOAS 1) $ runST (top $ dh)
  where
    top :: DefH -> ST s HOAS
    top (DefH n term) = do
      seen <- newSTRef (Set.empty)
      go term seen

    hash t = compText t 0

    go :: HOAS -> (STRef s (Set Text)) -> ST s HOAS
    go term seen = do
      let norm     = reduce term defs
      let termHash = hash term
      let normHash = hash norm
      -- traceM $ concat ["term: ",show term, " hash: ",show termH]
      -- traceM $ concat ["norm: ",show norm, " hash: ",show normH]
      seenSet <- readSTRef seen
      -- traceM $ concat ["seen: ",show seen']
      if | termHash `Set.member` seenSet -> return norm
         | normHash `Set.member` seenSet -> return norm
         | otherwise -> do
             modifySTRef' seen ((Set.insert termHash) . (Set.insert normHash))
             case norm of
               VarH n d -> return $ VarH n d
               RefH n h -> return $ RefH n h
               LamH n b -> return $ LamH n (\x -> unsafePerformST $ go (b x) seen)
               AppH f a -> AppH <$> (go f seen) <*> (go a seen)
               FixH n b -> go norm seen

normDef :: FilePath -> Name -> IO Term
normDef file name = do
  txt <- TIO.readFile file
  case parse' defs (ParseEnv [] (Defs M.empty M.empty)) file txt of
    Left  e  -> putStrLn (errorBundlePretty e) >> exitFailure
    Right ds -> case indexLookup name ds of
      Nothing -> putStrLn "Undefined Reference" >> exitFailure
      Just d  -> case toDefH d ds of
        Nothing -> putStrLn "Corrupt Cache" >> exitFailure
        Just dh -> return $ normalize dh ds

