{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Language.Yatima.GHC.Check where

import Language.Yatima.Term
import Language.Yatima.Defs
import Language.Yatima.GHC.Eval

import Data.Sequence (Seq, (|>), viewr, ViewR((:>), EmptyR))
import qualified Data.Sequence as Seq

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import           Data.Text                  (Text)
import qualified Data.Text                  as T

import Control.Monad.ST
import Control.Monad.Except
import Control.Monad.Trans
import Data.STRef

import Debug.Trace

-- TODO: share set of equals hashes between `equal` calls?
equal :: HOAS -> HOAS -> Defs -> Int -> Bool
equal a b defs dep = runST $ top a b dep
  where
    top :: HOAS -> HOAS -> Int -> ST s Bool
    top a b dep = do
      seen <- newSTRef (Set.empty)
      go a b dep seen

    go :: HOAS -> HOAS -> Int -> STRef s (Set (CID,CID)) -> ST s Bool
    go a b dep seen = do
      let var d = VarH noLoc "" d
      let a1 = reduce a defs
      let b1 = reduce b defs
      let ah = hash a1 0
      let bh = hash b1 0
      s' <- readSTRef seen
      if | (ah == bh)              -> return True
         | (ah,bh) `Set.member` s' -> return True
         | (bh,ah) `Set.member` s' -> return True
         | otherwise -> do
             modifySTRef' seen ((Set.insert (ah,bh)) . (Set.insert (bh,ah)))
             case (a1,b1) of
               (AllH _ _ au at ab, AllH _ _ bu bt bb) -> do
                 let a1_body = ab (var dep)
                 let b1_body = bb (var dep)
                 let rig_eq  = au == bu
                 bind_eq <- go at bt dep seen
                 body_eq <- go a1_body b1_body (dep+1) seen
                 return $ rig_eq && bind_eq && body_eq
               (LamH _ _ (Just (au,at)) ab, LamH _ _ (Just (bu,bt)) bb) -> do
                 let a1_body = ab (var dep)
                 let b1_body = bb (var dep)
                 let rig_eq  = au == bu
                 bind_eq <- go at bt dep seen
                 body_eq <- go a1_body b1_body (dep+1) seen
                 return $ rig_eq && bind_eq && body_eq
               (LamH _ _ Nothing ab, LamH _ _ Nothing bb) -> do
                 let a1_body = ab (var dep)
                 let b1_body = bb (var dep)
                 body_eq <- go a1_body b1_body (dep+1) seen
                 return $ body_eq
               (AppH _ af aa, AppH _ bf ba) -> do
                 func_eq <- go af bf dep seen
                 argm_eq <- go aa ba dep seen
                 return $ func_eq && argm_eq
               (LetH _ _ au at ax ab, LetH _ _ bu bt bx bb) -> do
                 let a1_body = ab ax
                 let b1_body = bb bx
                 let rig_eq  = au == bu
                 bind_eq <- go at bt dep seen
                 expr_eq <- go ax bx dep seen
                 body_eq <- go a1_body b1_body (dep+1) seen
                 return $ rig_eq && bind_eq && expr_eq && body_eq
               (SlfH _ _ ab, SlfH _ _ bb) -> do
                 let a1_body = ab (var dep)
                 let b1_body = bb (var dep)
                 go a1_body b1_body (dep+1) seen
               (NewH _ at ab, NewH _ bt bb) -> do
                 type_eq <- go at bt dep seen
                 body_eq <- go ab bb dep seen
                 return $ type_eq && body_eq
               (EliH _ ab, EliH _ bb) -> go ab bb dep seen
               (FixH _ _ ab, FixH _ _ bb) -> go (ab a1) (bb b1) (dep+1) seen
               (Op1H _ ap ax, Op1H _ bp bx) -> do
                 let prim_eq = ap == bp
                 argx_eq <- go ax bx dep seen
                 return $ prim_eq && argx_eq
               (Op2H _ ap ax ay, Op2H _ bp bx by) -> do
                 let prim_eq = ap == bp
                 argx_eq <- go ax bx dep seen
                 argy_eq <- go ay by dep seen
                 return $ prim_eq && argx_eq && argy_eq
               (IteH _ ac at af, IteH _ bc bt bf) -> do
                 cond_eq <- go ac bc dep seen
                 true_eq <- go at bt dep seen
                 fals_eq <- go af bf dep seen
                 return $ cond_eq && true_eq && fals_eq
               _ -> return False

data CheckErr
  = QuantityMismatch Loc Ctx Bool Uses Uses
  | TypeMismatch Loc Ctx Bool HOAS HOAS
  | EmptyContext Loc Ctx
  | UndefinedReference Loc Ctx Name CID
  | LambdaNonFunctionType Loc Ctx HOAS HOAS
  | NewNonSelfType Loc Ctx HOAS HOAS
  | EliNonSelfType Loc Ctx HOAS HOAS
  | CantInferNonAnnotatedLambda Loc Ctx HOAS
  | Prim1TypeError Loc Ctx Prim1 PrimType HOAS
  | Prim2TypeError Loc Ctx Prim2 PrimType HOAS HOAS
  | CustomErr Loc Ctx Text
  deriving Show

type Ctx      = Seq (Uses, HOAS)
--type PreCtx   = Seq (Uses, HOAS) -- should stand for contexts with only the Zero quantity

multiplyCtx :: Uses -> Ctx -> Ctx
multiplyCtx rho ctx = fmap mul ctx
  where mul (pi, typ) = (rho *# pi, typ)

-- Assumes both context are compatible (different only by quantities)
addCtx :: Ctx -> Ctx -> Ctx
addCtx ctx ctx' = Seq.zipWith add ctx ctx'
  where add (pi, typ) (pi', _) = (pi +# pi', typ)

mismatchMsg :: Bool -> Uses -> Uses -> Text
mismatchMsg linear found expected =
  T.concat ["Quantity mismatch.",
             "\nFound: ", T.pack $ show found,
             "\nExcepted: ", T.pack $ show expected,
             if linear then "" else " or less."]

term = toHOAS (Lam noLoc "x" Nothing (Var noLoc "x" 0)) [] 0
typ_ = toHOAS (All noLoc "x" Many (I64 noLoc) (Var noLoc "x" 0)) [] 0

check :: Bool -> Ctx -> Uses -> HOAS -> HOAS -> Defs -> Except CheckErr Ctx
check linear ctx rho trm expectType defs =
  case trm of
    LamH loc name Nothing termBody -> case reduce expectType defs of
      AllH _ _ pi bind expectTypeBody -> do
        let var = VarH noLoc name (length ctx)
        let ctx' = (ctx |> (Zero,bind))
        ctx' <- check linear ctx' Once (termBody var) (expectTypeBody var) defs
        case viewr ctx' of
          EmptyR -> throwError $ EmptyContext loc ctx
          ctx :> (pi', _) -> do
            when (if linear then pi' /= pi else pi' ># pi)
              (throwError (QuantityMismatch loc ctx linear pi' pi))
            return $ multiplyCtx rho ctx
    -- TODO
    LamH loc name (Just (annUses,annType)) termBody -> undefined

    LetH loc name pi exprType expr body -> do
      check linear ctx pi expr exprType defs
      let var = VarH noLoc name (length ctx)
      let ctx' = ctx |> (Zero, exprType)
      ctx' <- check linear ctx' Once (body var) expectType defs
      case viewr ctx' of
        EmptyR -> throwError $ EmptyContext loc ctx
        ctx :> (pi', _) -> do
          when (if linear then pi' /= pi else pi' ># pi)
            (throwError (QuantityMismatch loc ctx linear pi' pi))
          return $ multiplyCtx rho (addCtx ctx ctx')
    _ -> do
      (ctx, infr) <- infer linear ctx rho trm defs
      if equal expectType infr defs (length ctx)
        then return ctx
        else throwError (TypeMismatch noLoc ctx linear expectType infr)


infer :: Bool -> Ctx -> Uses -> HOAS -> Defs -> Except CheckErr (Ctx, HOAS)
infer linear ctx rho term defs =
  case term of
    VarH l n idx -> do
      let (_, typ) = Seq.index ctx idx
      let ctx' = Seq.update idx (rho, typ) ctx
      return (ctx', typ)
    RefH l n c -> case deref c defs of
      Just d  -> return (ctx, defToHOAS d)
      Nothing -> throwError $ UndefinedReference l ctx n c
    AppH loc func argm -> do
      (ctx, funcType) <- infer linear ctx rho func defs
      case reduce funcType defs of
        AllH _ _ pi bind body -> do
          ctx' <- check linear ctx (rho *# pi) argm bind defs
          return (addCtx ctx ctx', body argm)
        x -> throwError $ LambdaNonFunctionType loc ctx func x
    LamH loc nam Nothing body -> do
      throwError $ CantInferNonAnnotatedLambda loc ctx term

    -- TODO
    LamH loc nam (Just (uses,typ_)) body -> undefined

    TypH l   -> return (ctx, TypH l)
    I64H l   -> return (ctx, TypH l)
    F64H l   -> return (ctx, TypH l)
    WrdH l _ -> return (ctx, I64H l)
    DblH l _ -> return (ctx, F64H l)

    SlfH l name body -> do
      let selfVar = VarH noLoc name $ length ctx
      let ctx' = ctx |> (Zero, term)
      check linear ctx' Zero (body selfVar) (TypH noLoc) defs
      return (ctx, TypH noLoc)
    NewH loc typ_ body -> do
      case reduce typ_ defs of
        t@(SlfH _ _ b) -> do
          check linear ctx Zero t (TypH noLoc) defs
          check linear ctx Zero body (b t) defs
          return (ctx, t)
        x        -> throwError $ NewNonSelfType loc ctx term x
    EliH loc body -> do
       (ctx', bodyType) <- infer linear ctx rho body defs
       case reduce bodyType defs of
        t@(SlfH _ _ b) -> return (ctx, b t)
        x        -> throwError $ EliNonSelfType loc ctx term x

    AllH loc name pi bind body -> do
      let name_var = VarH noLoc name $ length ctx
      let ctx'     = ctx |> (Zero, bind)
      check linear ctx  Zero bind (TypH noLoc) defs
      check linear ctx' Zero (body name_var) (TypH noLoc) defs
      return (ctx, TypH noLoc)
    LetH loc name pi exprType expr body -> do
      check linear ctx pi expr typ_ defs
      let exprVar = VarH noLoc name (length ctx)
      let ctx' = ctx |> (Zero, exprType)
      (ctx', typ) <- infer linear ctx' Once (body exprVar) defs
      case viewr ctx' of
        EmptyR                -> throwError (EmptyContext loc ctx)
        ctx' :> (pi', _) -> do
          when (if linear then pi' /= pi else pi' ># pi)
            (throwError (QuantityMismatch loc ctx linear pi' pi))
          return (multiplyCtx rho (addCtx ctx ctx'), typ)
    -- TODO
    FixH l n b   -> undefined
    Op1H l p a   -> case prim1Type p of
      IUna -> check linear ctx Zero a (I64H noLoc) defs >> return (ctx, I64H noLoc)
      ICnv -> check linear ctx Zero a (F64H noLoc) defs >> return (ctx, I64H noLoc)
      FUna -> check linear ctx Zero a (F64H noLoc) defs >> return (ctx, F64H noLoc)
      FCnv -> check linear ctx Zero a (I64H noLoc) defs >> return (ctx, F64H noLoc)
      x    -> throwError (Prim1TypeError l ctx p x a)
    Op2H l p a b -> case prim2Type p of
      IRel -> do
        check linear ctx Zero a (I64H noLoc) defs
        check linear ctx Zero b (I64H noLoc) defs
        return (ctx, I64H noLoc)
      IBin -> do
        check linear ctx Zero a (I64H noLoc) defs
        check linear ctx Zero b (I64H noLoc) defs
        return (ctx, I64H noLoc)
      FRel -> do
        check linear ctx Zero a (F64H noLoc) defs
        check linear ctx Zero b (F64H noLoc) defs
        return (ctx, I64H noLoc)
      FBin -> do
        check linear ctx Zero a (F64H noLoc) defs
        check linear ctx Zero b (F64H noLoc) defs
        return (ctx, F64H noLoc)
      x    -> throwError (Prim2TypeError l ctx p x a b)
    -- Add return type annotation to Ite?
    IteH l c t f -> do
      check linear ctx Zero c (I64H noLoc) defs
      (ctx, tt) <- infer linear ctx Zero t defs
      check linear ctx Zero f tt defs
      return (ctx, tt)
--
--checkExpr :: Bool -> Expr -> Module -> Except CheckErr ()
--checkExpr linear (Expr n typ trm) mod = do
--  --traceM $ "checking: " ++ T.unpack n
--  --traceM $ "type: " ++ show typ
--  --traceM $ "term: " ++ show trm
--  check linear Seq.empty One trm typ mod
--  return ()
--
--checkModule :: Bool -> Module -> Except CheckErr ()
--checkModule linear mod = forM_ (Map.toList $ _defs mod) (\(n,x) -> checkExpr linear x mod)
