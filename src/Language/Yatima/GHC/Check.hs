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
               (LamH _ _ au at ab, LamH _ _ bu bt bb) -> do
                 let a1_body = ab (var dep)
                 let b1_body = bb (var dep)
                 let rig_eq  = au == bu
                 bind_eq <- go at bt dep seen
                 body_eq <- go a1_body b1_body (dep+1) seen
                 return $ rig_eq && bind_eq && body_eq
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
               (OprH _ ap ax ay, OprH _ bp bx by) -> do
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
  | ImplementationBugEmptyContext Loc Ctx
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

--mismatchMsg :: Bool -> Uses -> Uses -> Text
--mismatchMsg linear found expected =
--  T.concat ["Quantity mismatch.",
--             "\nFound: ", T.pack $ show found,
--             "\nExcepted: ", T.pack $ show expected,
--             if linear then "" else " or less."]

check :: Bool -> Ctx -> Uses -> HOAS -> HOAS -> Defs -> Except CheckErr Ctx
check affine ctx rho trm typ defs =
  case trm of
    LamH loc name uses trm_typ trm_body -> case reduce trm_typ defs of
      AllH _ _ pi bind typ_body -> do
        let var = VarH noLoc name (length ctx)
        let ctx' = (ctx |> (Zero,bind))
        ctx' <- check affine ctx' Once (trm_body var) (typ_body var) defs
        case viewr ctx' of
          EmptyR -> throwError $ ImplementationBugEmptyContext loc ctx
          ctx :> (pi', _) -> do
            when (if linear then pi' /= pi else pi' ># pi)
     --       unless (if linear then pi' == pi else pi' ≤# pi)
     --         (throwError (QuantityMismatch loc ctx linear pi' pi))
     --       return $ multiplyCtx rho ctx
      _ -> do
        throwError (CustomErr noLoc ctx "Impossible")
    _ -> do
      throwError (CustomErr noLoc ctx "Impossible")

     -- AllH _ _ pi bind typ_body -> do
     --   let var = VarH noLoc name (length prectx)
     --   let prectx'  = prectx |> (Zero, bind)
     --   ctx' <- check linear prectx' Once (trm_body var) (typ_body trm var) defs
     --   case viewr ctx' of
     --     EmptyR               -> throwError (CustomErr loc ctx "Impossible")
     --     ctx :> (pi', _) -> do
     --       unless (if linear then pi' == pi else pi' ≤# pi)
     --         (throwError (QuantityMismatch loc ctx linear pi' pi))
     --       return $ multiplyCtx rho ctx
      --_  -> do
      --  throwError (CustomErr loc ctx "Lambda has non-function type")
--    Let loc π name expr body -> do
--      (ctx, expr_typ) <- infer linear prectx π expr defs
--      let var = Var noLoc name (length prectx)
--      let prectx' = prectx |> (Zero, expr_typ)
--      ctx' <- check linear prectx' One (body var) typ defs
--      case viewr ctx' of
--        EmptyR                -> throwError (CheckErr loc prectx "Impossible")
--        ctx' :> (π', _) -> do
--          unless (if linear then π' == π else π' ≤# π)
--            (throwError (CheckErr loc prectx $ mismatchMsg linear π' π))
--          return $ multiplyCtx ρ (addCtx ctx ctx')
--    _ -> do
--      (ctx, infr) <- infer linear prectx ρ trm defs
--      if equal typ infr defs (length prectx)
--        then return ctx
--        else do
--        let errMsg = T.concat ["Found type... \x1b[2m", term $ normalize infr defs False, "\x1b[0m\n",
--                               "Instead of... \x1b[2m", term $ normalize typ defs False,  "\x1b[0m"]
--        throwError (CheckErr noLoc prectx errMsg)

----infer :: Bool -> PreCtx -> Rig -> Term -> Module -> Except CheckErr (Ctx, TermType)
----infer linear prectx ρ trm defs =
----  case trm of
----    Var l n idx -> do
----      let (_, typ) = Seq.index prectx idx
----      let ctx = Seq.update idx (ρ, typ) prectx
----      return (ctx, typ)
----    Ref l n -> case (_defs defs) Map.!? n of
----      Just (Expr _ t _) -> return (prectx, t)
----      Nothing           -> throwError (CheckErr l prectx (T.concat ["Undefined reference ", n]))
----    Typ l   -> return (prectx, Typ l)
----    All loc π self name bind body -> do
----      let self_var = Var noLoc self $ length prectx
----      let name_var = Var noLoc name $ length prectx + 1
----      let prectx'  = prectx |> (Zero, trm) |> (Zero, bind)
----      check linear prectx Zero bind (Typ noLoc) defs
----      check linear prectx' Zero (body self_var name_var) (Typ noLoc) defs
----      return (prectx, Typ noLoc)
----    App loc _ func argm -> do
----      (ctx, func_typ') <- infer linear prectx ρ func defs
----      let func_typ = reduce func_typ' defs False
----      case func_typ of
----        All _ π _ _ bind body -> do
----          ctx' <- check linear prectx (ρ *# π) argm bind defs
----          let typ = body func argm
----          return (addCtx ctx ctx', typ)
----        _ -> throwError $ CheckErr loc ctx "Non-function application"
----    Let loc π name expr body -> do
----      (ctx, expr_typ) <- infer linear prectx π expr defs
----      let expr_var = Var noLoc name (length prectx)
----      let prectx' = prectx |> (Zero, expr_typ)
----      (ctx', typ) <- infer linear prectx' One (body expr_var) defs
----      case viewr ctx' of
----        EmptyR                -> throwError (CheckErr loc prectx "Impossible")
----        ctx' :> (π', _) -> do
----          unless (if linear then π' == π else π' ≤# π)
----            (throwError (CheckErr loc prectx  $ mismatchMsg linear π' π))
----          return (multiplyCtx ρ (addCtx ctx ctx'), typ)
----    _ -> throwError $ CheckErr noLoc prectx "Cannot infer type"
----
----checkExpr :: Bool -> Expr -> Module -> Except CheckErr ()
----checkExpr linear (Expr n typ trm) mod = do
----  --traceM $ "checking: " ++ T.unpack n
----  --traceM $ "type: " ++ show typ
----  --traceM $ "term: " ++ show trm
----  check linear Seq.empty One trm typ mod
----  return ()
----
----checkModule :: Bool -> Module -> Except CheckErr ()
----checkModule linear mod = forM_ (Map.toList $ _defs mod) (\(n,x) -> checkExpr linear x mod)
