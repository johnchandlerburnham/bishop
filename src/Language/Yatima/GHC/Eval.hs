{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TupleSections #-}
{-|
Module : Language.Yatima.GHC.Eval
Description : Evaluates exprassions in the Yatima Language using GHC
Copyright   : (c) Sunshine Cybernetics, 2020
License     : AGPL-3
Maintainer  : john@sunshinecybernetics.com
Stability   : experimental
-}
module Language.Yatima.GHC.Eval where

import           Control.Monad.ST
import           Control.Monad.ST.UnsafePerform
import           Control.Monad.Except

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

-- | Higher-Order Abstract Syntax term which uses the Glasgow Haskell compiler's
-- native functions as our reduction system.
data HOAS where
  VarH :: Loc -> Name -> Int -> HOAS
  RefH :: Loc -> Name -> CID -> HOAS
  LamH :: Loc -> Name -> Maybe (Uses,HOAS) -> (HOAS -> HOAS) -> HOAS
  AppH :: Loc -> HOAS -> HOAS -> HOAS
  LetH :: Loc -> Name -> Uses -> HOAS -> HOAS -> (HOAS -> HOAS) -> HOAS

  TypH :: Loc -> HOAS
  AllH :: Loc -> Name -> Uses -> HOAS -> (HOAS -> HOAS) -> HOAS
  SlfH :: Loc -> Name -> (HOAS -> HOAS) -> HOAS
  NewH :: Loc -> HOAS -> HOAS -> HOAS
  EliH :: Loc -> HOAS -> HOAS

  WrdH :: Loc -> Word64 -> HOAS
  I64H :: Loc -> HOAS
  DblH :: Loc -> Double -> HOAS
  F64H :: Loc -> HOAS
  Op1H :: Loc -> Prim1 -> HOAS -> HOAS
  Op2H :: Loc -> Prim2 -> HOAS -> HOAS -> HOAS
  IteH :: Loc -> HOAS -> HOAS -> HOAS -> HOAS

  FixH :: Loc -> Name -> (HOAS -> HOAS) -> HOAS

findCtx :: Int -> [HOAS] -> Maybe HOAS
findCtx i cs = go cs 0
  where
    go (c:cs) j
      | i == j   = Just c
      | otherwise = go cs (j+1)
    go [] _     = Nothing

toHOAS :: Term -> [HOAS] -> Int -> HOAS
toHOAS t ctx dep = case t of
  Var l n i       -> case findCtx i ctx of
    Just trm -> trm
    Nothing  -> VarH l n (dep - i - 1)
  Ref l n h       -> RefH l n h
  Lam l n (Just (u,t)) b   -> LamH l n (Just (u,go t)) (\x -> bind x b)
  Lam l n Nothing      b   -> LamH l n Nothing         (\x -> bind x b)
  App l f a       -> AppH l (go f) (go a)
  Let l n u t d b -> LetH l n u (go t) (FixH l n (\x -> bind x d)) (\x -> bind x b)
  Typ l           -> TypH l
  All l n u t b   -> AllH l n u (go t) (\x -> bind x b)
  Slf l n b       -> SlfH l n (\x -> bind x b)
  New l t b       -> NewH l (go t) (go b)
  Eli l x         -> EliH l (go x)
  Wrd l w         -> WrdH l w
  Dbl l d         -> DblH l d
  I64 l           -> I64H l
  F64 l           -> F64H l
  Op1 l p a       -> Op1H l p (go a)
  Op2 l p a b     -> Op2H l p (go a) (go b)
  Ite l c t f     -> IteH l (go c) (go t) (go f)
  where
    bind x t = toHOAS t (x:ctx) (dep + 1)
    go t     = toHOAS t ctx dep

fromHOAS :: HOAS -> Int -> Term
fromHOAS t dep = case t of
  FixH l n b       -> go (b (FixH l n b))
  VarH l n i       -> Var l n (dep - i - 1)
  RefH l n h       -> Ref l n h
  LamH l n (Just (u,t)) b   -> Lam l n (Just (u,go t)) (unbind n b)
  LamH l n Nothing      b   -> Lam l n Nothing (unbind n b)
  AppH l f a       -> App l (go f) (go a)
  LetH l n u t d b -> Let l n u (go t) (go d) (unbind n b)
  TypH l           -> Typ l
  AllH l n u t b   -> All l n u (go t) (unbind n b)
  SlfH l n b       -> Slf l n (unbind n b)
  NewH l t b       -> New l (go t) (go b)
  EliH l x         -> Eli l (go x)
  WrdH l w         -> Wrd l w
  DblH l d         -> Dbl l d
  I64H l           -> I64 l
  F64H l           -> F64 l
  Op1H l p a       -> Op1 l p (go a)
  Op2H l p a b     -> Op2 l p (go a) (go b)
  IteH l c t f     -> Ite l (go c) (go t) (go f)
  where
    go t       = fromHOAS t dep
    unbind n b = fromHOAS (b (VarH noLoc n dep)) (dep + 1)

defToHOAS :: DefDeref -> HOAS
defToHOAS (DefDeref _ anon meta _ _) =
  let term = resaturate anon meta
      name = (_names meta) IM.! 0
      loc  = (_locs meta) IM.! 0
   in (FixH loc name (\s -> toHOAS term [s] 1))

printHOAS :: HOAS -> Text
printHOAS = prettyTerm . (\x -> fromHOAS x 0)

instance Show HOAS where
  show t = T.unpack $ printHOAS t

reduce :: HOAS -> Defs -> HOAS
reduce t ds = case t of
  FixH l n b       -> go (b (FixH l n b))
  RefH _ n c       -> case deref c ds of
    Just d  -> go $ defToHOAS d
    Nothing -> error "BAD: Undefined Reference during reduction"
  LamH l n ut b    -> LamH l n ut b
  AppH l f a       -> case go f of
    LamH _ _ _ b -> go (b a)
    x            -> AppH l f a
  LetH _ n u t d b -> go (b d)
  Op1H l p a       -> case (prim1Type p, go a) of
    (IUna, WrdH _ a) -> WrdH noLoc (opIUna p a)
    (ICnv, DblH l a) -> either
      (\ _ -> Op1H noLoc p (DblH l a))
      (\ x -> WrdH noLoc x)
      (runExcept $ opICnv p a)
    (FUna, DblH _ a) -> DblH noLoc (opFUna p a)
    (FCnv, WrdH l a) -> DblH noLoc (opFCnv p a)
    (_   , a       ) -> Op1H l p a
  -- Op2 is uncurried. This simplifies the WASM operations, and curried forms of
  -- the binary operations can be created at the language layer with `Lam`
  Op2H l p a b     -> case (prim2Type p, go a, go b) of
    (IRel, WrdH _ a, WrdH _ b) -> WrdH noLoc (opIRel p a b)
    (IBin, WrdH la a, WrdH lb b) -> either
      (\ _ -> Op2H noLoc p (WrdH la a) (WrdH lb b))
      (\ x -> WrdH noLoc x)
      (runExcept $ opIBin p a b)
    (FRel, DblH _ a, DblH _ b) -> WrdH noLoc (opFRel p a b)
    (FBin, DblH _ a, DblH _ b) -> DblH noLoc (opFBin p a b)
    (_   ,        a,        b) -> Op2H l p a b
  IteH l c t f     -> case go c of
    WrdH _ 0 -> go f
    WrdH _ _ -> go t
    _        -> IteH l c t f
  _                -> t
  where
    go x = reduce x ds

reduceName :: Name -> Defs -> Maybe Term
reduceName name ds = do
  cid             <- indexLookup name ds
  def             <- deref cid ds
  return $ (flip fromHOAS 0) $ reduce (defToHOAS def) ds

hash :: HOAS -> Int -> CID
hash term dep = makeCID $ fst $ (desaturate "" noLoc) (fromHOAS term dep)

normalize :: HOAS -> Defs -> HOAS
normalize term defs = runST (top $ term)
  where
    top :: HOAS -> ST s HOAS
    top term = do
      seen <- newSTRef (Set.empty)
      go term seen

    go :: HOAS -> (STRef s (Set CID)) -> ST s HOAS
    go term seen = do
      let norm     = reduce term defs
      let termHash = hash term 0
      let normHash = hash norm 0
      -- traceM $ concat ["term: ",show term, " hash: ",show termH]
      -- traceM $ concat ["norm: ",show norm, " hash: ",show normH]
      seenSet <- readSTRef seen
      -- traceM $ concat ["seen: ",show seen']
      if | termHash `Set.member` seenSet -> return norm
         | normHash `Set.member` seenSet -> return norm
         | otherwise -> do
             modifySTRef' seen ((Set.insert termHash) . (Set.insert normHash))
             case norm of
               LamH l n (Just (u,t)) b   -> do
                 bind <- Just . (u,) <$> go t seen
                 return $ LamH l n bind (\x -> unsafePerformST $ go (b x) seen)
               LamH l n Nothing b   -> do
                 return $ LamH l n Nothing (\x -> unsafePerformST $ go (b x) seen)
               AllH l n u t b   -> do
                 bind <- go t seen
                 return $ AllH l n u bind (\x -> unsafePerformST $ go (b x) seen)
               AppH l f a       -> AppH l <$> (go f seen) <*> (go a seen)
               Op1H l p x       -> Op1H l p <$> (go x seen)
               Op2H l p x y     -> Op2H l p <$> (go x seen) <*> (go y seen)
               IteH l c t f     ->
                 IteH l <$> (go c seen) <*> (go t seen) <*> (go f seen)
               _                -> return $ norm

normName :: Name -> Defs -> Maybe Term
normName name ds = do
  cid             <- indexLookup name ds
  def             <- deref cid ds
  return $ (flip fromHOAS 0) $ normalize (defToHOAS def) ds
