{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE MultiWayIf #-}
{-|
Module : Language.Yatima.Eval
Description : Evaluates exprassions in the Yatima Language using GHC
Copyright   : (c) Sunshine Cybernetics, 2020
License     : AGPL-3
Maintainer  : john@sunshinecybernetics.com
Stability   : experimental
-}
module Language.Yatima.Eval where

import           Control.Monad.ST
import           Control.Monad.ST.UnsafePerform

import           Data.IntMap                    (IntMap)
import qualified Data.IntMap                    as IM
import           Data.Map                       (Map)
import qualified Data.Map                       as M
import           Data.Set                       (Set)
import qualified Data.Set                       as Set
import           Data.STRef
import           Data.Text                      (Text)
import qualified Data.Text                      as T
import qualified Data.Text.IO                   as TIO
import           Data.Word

import qualified Data.ByteString.Lazy           as BSL

import           Data.IPLD.CID

import           System.Exit

import           Codec.Serialise

import           Language.Yatima.Term
import           Language.Yatima.Defs

data HOAS where
  VarH :: Name -> Int -> HOAS
  RefH :: Name -> CID -> HOAS
  LamH :: Name -> Uses -> HOAS -> (HOAS -> HOAS) -> HOAS
  AppH :: HOAS -> HOAS -> HOAS
  LetH :: Name -> Uses -> HOAS -> HOAS -> (HOAS -> HOAS) -> HOAS

  TypH :: HOAS
  AllH :: Name -> Uses -> HOAS -> (HOAS -> HOAS) -> HOAS
  SlfH :: Name -> (HOAS -> HOAS) -> HOAS
  NewH :: HOAS -> HOAS -> HOAS
  EliH :: HOAS -> HOAS

  WrdH :: Word64 -> HOAS
  I64H :: HOAS
  DblH :: Double -> HOAS
  F64H :: HOAS
  OprH :: Prim -> HOAS -> HOAS -> HOAS
  IteH :: HOAS -> HOAS -> HOAS -> HOAS

  FixH :: Name -> (HOAS -> HOAS) -> HOAS

findCtx :: Int -> [HOAS] -> Maybe HOAS
findCtx i cs = go cs 0
  where
    go (c:cs) j
      | i == j   = Just c
      | otherwise = go cs (j+1)
    go [] _     = Nothing

toHOAS :: Term -> [HOAS] -> Int -> HOAS
toHOAS t ctx dep = case t of
  Var _ n i       -> case findCtx i ctx of
    Just trm -> trm
    Nothing  -> VarH n (dep - i - 1)
  Ref _ n h       -> RefH n h
  Lam _ n u t b   -> LamH n u (go t) (\x -> bind x b)
  App _ f a       -> AppH (go f) (go a)
  Let _ n u t d b -> LetH n u (go t) (FixH n (\x -> bind x d)) (\x -> bind x b)
  Typ _           -> TypH
  All _ n u t b   -> AllH n u (go t) (\x -> bind x b)
  Slf _ n b       -> SlfH n (\x -> bind x b)
  New _ t b       -> NewH (go t) (go b)
  Eli _ x         -> EliH (go x)
  Wrd _ w         -> WrdH w
  Dbl _ d         -> DblH d
  Opr _ p a b     -> OprH p (go a) (go b)
  Ite _ c t f     -> IteH (go c) (go t) (go f)
  where
    bind x t = toHOAS t (x:ctx) (dep + 1)
    go t     = toHOAS t ctx dep

fromHOAS :: HOAS -> Int -> Term
fromHOAS t dep = case t of
  FixH n b       -> go (b (FixH n b))
  VarH n i       -> Var noLoc n (dep - i - 1)
  RefH n h       -> Ref noLoc n h
  LamH n u t b   -> Lam noLoc n u (go t) (unbind n b)
  AppH f a       -> App noLoc (go f) (go a)
  LetH n u t d b -> Let noLoc n u (go t) (go d) (unbind n b)
  TypH           -> Typ noLoc
  AllH n u t b   -> All noLoc n u (go t) (unbind n b)
  SlfH n b       -> Slf noLoc n (unbind n b)
  NewH t b       -> New noLoc (go t) (go b)
  EliH x         -> Eli noLoc (go x)
  WrdH w         -> Wrd noLoc w
  DblH d         -> Dbl noLoc d
  OprH p a b     -> Opr noLoc p (go a) (go b)
  IteH c t f     -> Ite noLoc (go c) (go t) (go f)
  where
    go t       = fromHOAS t dep
    unbind n b = fromHOAS (b (VarH n dep)) (dep + 1)

defToHOAS :: DefDeref -> HOAS
defToHOAS (DefDeref _ anon meta _ _) =
  let term = resaturate anon meta
      name = (_names meta) IM.! 0
   in (FixH name (\s -> toHOAS term [s] 1))

printHOAS :: HOAS -> Text
printHOAS = prettyTerm . (\x -> fromHOAS x 0)

reduce :: HOAS -> Defs -> HOAS
reduce t ds = case t of
  FixH n b       -> go (b (FixH n b))
  RefH n c       -> case deref c ds of
    Just d  -> go $ defToHOAS d
    Nothing -> error "BAD: Undefined Reference during reduction"
  LamH n u t b   -> LamH n u t b
  AppH f a       -> case go f of
    LamH _ _ _ bdy -> go (bdy a)
    x              -> AppH f a

  LetH n u t d b -> go (b d)
  OprH p a b     -> case (go a, go b) of
    (WrdH x,WrdH y) -> maybe t unPrim (op p (W x) (W y))
    (WrdH x,DblH y) -> maybe t unPrim (op p (W x) (D y))
    (DblH x,WrdH y) -> maybe t unPrim (op p (D x) (W y))
    (DblH x,DblH y) -> maybe t unPrim (op p (D x) (D y))
    _               -> t
  IteH c t f     -> case go c of
    WrdH 0 -> go f
    WrdH _ -> go t
    _      -> IteH c t f
  _              -> t
  where
    go x = reduce x ds
    unPrim (W x) = WrdH x
    unPrim (D x) = DblH x

reduceName :: Name -> Defs -> Maybe Term
reduceName name ds = do
  cid             <- indexLookup name ds
  def             <- deref cid ds
  return $ (flip fromHOAS 0) $ reduce (defToHOAS def) ds

hash :: HOAS -> Int -> CID
hash term dep = makeCID $ fst $ (desaturate "" noLoc) (fromHOAS term dep)

--let go = compText in case term of
--  VarH n x -> if x < 0
--              then T.concat ["^", T.pack $ show $ dep + x]
--              else T.concat ["#", T.pack $ show x]
--  RefH n h -> T.concat ["&", n] 
--  FixH _ b -> T.concat ["μ", go (b (VarH "" (0-dep-1))) (dep+1)]
--  LamH n b -> T.concat ["λ", go (b (VarH "" (0-dep-1))) (dep+1)]
--  AppH f a -> T.concat ["@", go f dep, go a dep]
----
----normalize :: DefH -> Defs -> Term
----normalize dh defs = (flip fromHOAS 1) $ runST (top $ dh)
----  where
----    top :: DefH -> ST s HOAS
----    top (DefH n term) = do
----      seen <- newSTRef (Set.empty)
----      go term seen
----
----    hash t = compText t 0
----
----    go :: HOAS -> (STRef s (Set Text)) -> ST s HOAS
----    go term seen = do
----      let norm     = reduce term defs
----      let termHash = hash term
----      let normHash = hash norm
----      -- traceM $ concat ["term: ",show term, " hash: ",show termH]
----      -- traceM $ concat ["norm: ",show norm, " hash: ",show normH]
----      seenSet <- readSTRef seen
----      -- traceM $ concat ["seen: ",show seen']
----      if | termHash `Set.member` seenSet -> return norm
----         | normHash `Set.member` seenSet -> return norm
----         | otherwise -> do
----             modifySTRef' seen ((Set.insert termHash) . (Set.insert normHash))
----             case norm of
----               VarH n d -> return $ VarH n d
----               RefH n h -> return $ RefH n h
----               LamH n b -> return $ LamH n (\x -> unsafePerformST $ go (b x) seen)
----               AppH f a -> AppH <$> (go f seen) <*> (go a seen)
----               FixH n b -> go norm seen
----
----normDef :: FilePath -> Name -> IO Term
----normDef file name = do
----  txt <- TIO.readFile file
----  case parse' defs (ParseEnv [] (Defs M.empty M.empty)) file txt of
----    Left  e  -> putStrLn (errorBundlePretty e) >> exitFailure
----    Right ds -> case indexLookup name ds of
----      Nothing -> putStrLn "Undefined Reference" >> exitFailure
----      Just d  -> case toDefH d ds of
----        Nothing -> putStrLn "Corrupt Cache" >> exitFailure
----        Just dh -> return $ normalize dh ds
----
