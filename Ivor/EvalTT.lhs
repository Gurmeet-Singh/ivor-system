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

Specialise a pattern matching definition - support for 'spec'

> specialise :: Context -> PMFun Name ->
>               [(Name, ([Int], Int))] -> -- functions with static args
>               [Name] -> -- frozen names
>               (PMFun Name, Context, [Name]) -- also, new names
> specialise ctxt (PMFun ar ps) statics frozen = sp ctxt ps [] []
>   where
>    sp ctxt [] names acc = (PMFun ar (reverse acc), ctxt, names)
>    sp ctxt@(Ctxt st) (p@(Sch args env ret):ps) names acc
>         = let ret' = eval_nf_limit (defs st) ret
>                          (map (\x -> (x,0)) frozen)
>                          (Just statics) in
>           sp ctxt ps names (Sch args env ret' : acc)

    sp ctxt (p@(PWithClause eq args scr pats):ps) names acc
         = let (pats', ctxt', names') = specialise ctxt pats statics frozen in
               sp ctxt' ps names' (p:acc)
