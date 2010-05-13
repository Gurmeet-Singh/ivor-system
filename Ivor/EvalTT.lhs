> -- |
> -- Module      : Ivor.TT
> -- Copyright   : Edwin Brady
> -- Licence     : BSD-style (see LICENSE in the distribution)
> --
> -- Maintainer  : eb@dcs.st-and.ac.uk
> -- Stability   : experimental
> -- Portability : non-portable
> --
> -- Public interface to evaluator.

> module Ivor.EvalTT where

> import Ivor.Evaluator
> import Ivor.CtxtTT
> import Ivor.Values
> import Ivor.ViewTerm as VTerm
> import Ivor.State
> import Ivor.Nobby
> import Ivor.TTCore
> import Ivor.Typecheck
> import qualified Ivor.Tactics as Tactics

> -- |Normalise a term and its type (using old evaluator_
> eval :: Context -> Term -> Term
> eval (Ctxt st) (Term (tm,ty)) = Term (normalise (defs st) tm,
>                                       normalise (defs st) ty)

> -- |Reduce a term and its type to Weak Head Normal Form
> whnf :: Context -> Term -> Term
> whnf (Ctxt st) (Term (tm,ty)) = Term (eval_whnf (defs st) tm,
>                                          eval_whnf (defs st) ty)

> -- |Reduce a term and its type to Normal Form (using new evaluator)
> evalnew :: Context -> Term -> Term
> evalnew (Ctxt st) (Term (tm,ty)) = Term (tidyNames (eval_nf (defs st) tm),
>                                          tidyNames (eval_nf (defs st) ty))

> -- |Reduce a term and its type to Normal Form (using new evaluator, not
> -- reducing given names)
> evalnewWithout :: Context -> Term -> [Name] -> Term
> evalnewWithout (Ctxt st) (Term (tm,ty)) ns 
>                    = Term (tidyNames (eval_nf_without (defs st) tm ns),
>                            tidyNames (eval_nf_without (defs st) ty ns))

> -- |Reduce a term and its type to Normal Form (using new evaluator, reducing
> -- given names a maximum number of times)
> evalnewLimit :: Context -> Term -> [(Name, Int)] -> Term
> evalnewLimit (Ctxt st) (Term (tm,ty)) ns 
>                  = Term (eval_nf_limit (defs st) tm ns Nothing,
>                          eval_nf_limit (defs st) ty ns Nothing)

> -- |Evaluate a term in the context of the given goal
> evalCtxt :: (IsTerm a) => Context -> Goal -> a -> TTM Term
> evalCtxt (Ctxt st) goal tm =
>     do rawtm <- raw tm
>        prf <- case proofstate st of
>                 Nothing -> fail "No proof in progress"
>                 Just x -> return x
>        let h = case goal of
>                (Goal x) -> x
>                DefaultGoal -> head (holequeue st)
>        case (Tactics.findhole (defs st) (Just h) prf holeenv) of
>          (Just env) -> do (tm, ty) <- tt $ Ivor.Typecheck.check (defs st) env rawtm Nothing
>                           let tnorm = normaliseEnv env (defs st) tm
>                           return $ Term (tnorm, ty)
>          Nothing -> fail "No such goal"
>  where holeenv :: Gamma Name -> Env Name -> Indexed Name -> Env Name
>        holeenv gam hs _ = Tactics.ptovenv hs

