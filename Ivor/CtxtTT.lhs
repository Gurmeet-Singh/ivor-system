> -- |
> -- Module      : Ivor.CtxtTT
> -- Copyright   : Edwin Brady
> -- Licence     : BSD-style (see LICENSE in the distribution)
> --
> -- Maintainer  : eb@dcs.st-and.ac.uk
> -- Stability   : experimental
> -- Portability : non-portable
> --
> -- Public interface to ivor contexts.

> module Ivor.CtxtTT where

> import Ivor.TTCore as TTCore
> import Ivor.Errors
> import Ivor.ViewTerm as VTerm
> import Ivor.State
> import Control.Monad.Error(Error,noMsg,strMsg)

> data TTError = CantUnify ViewTerm ViewTerm
>              | NotConvertible ViewTerm ViewTerm
>              | Message String
>              | Unbound ViewTerm ViewTerm ViewTerm ViewTerm [Name]
>              | NoSuchVar Name
>              | CantInfer Name ViewTerm
>              | ErrContext String TTError
>              | AmbiguousName [Name]

> type TTM = Either TTError

> ttfail :: String -> TTM a
> ttfail s = Left (Message s)

> tt :: IvorM a -> TTM a
> tt (Left err) = Left (getError err)
> tt (Right v) = Right v

> getError :: IError -> TTError
> getError (ICantUnify l r) = CantUnify (view (Term (l, Ind TTCore.Star))) (view (Term (r, Ind TTCore.Star)))
> getError (INotConvertible l r) = NotConvertible (view (Term (l, Ind TTCore.Star))) (view (Term (r, Ind TTCore.Star)))
> getError (IMessage s) = Message s
> getError (IUnbound clause clty rhs rhsty names)
>              = Unbound (view (Term (clause, Ind TTCore.Star)))
>                        (view (Term (clty, Ind TTCore.Star)))
>                        (view (Term (rhs, Ind TTCore.Star)))
>                        (view (Term (rhsty, Ind TTCore.Star)))
>                        names
> getError (ICantInfer nm tm) = CantInfer nm (view (Term (tm, Ind TTCore.Star)))
> getError (INoSuchVar n) = NoSuchVar n
> getError (IAmbiguousName ns) = AmbiguousName ns
> getError (IContext s e) = ErrContext s (getError e)

> instance Show TTError where
>     show (CantUnify t1 t2) = "Can't unify " ++ show t1 ++ " and " ++ show t2
>     show (NotConvertible t1 t2) = show t1 ++ " and " ++ show t2 ++ " are not convertible"
>     show (Message s) = s
>     show (Unbound clause clty rhs rhsty ns)
>        = show ns ++ " unbound in clause " ++ show clause ++ " : " ++ show clty ++
>                     " = " ++ show rhs
>     show (CantInfer  n tm) = "Can't infer value for " ++ show n ++ " in " ++ show tm
>     show (NoSuchVar n) = "No such name as " ++ show n
>     show (AmbiguousName ns) = "Ambiguous name " ++ show ns
>     show (ErrContext c err) = c ++ show err

> instance Error TTError where
>     noMsg = Message "Ivor Error"
>     strMsg s = Message s

> -- | Abstract type representing state of the system.
> newtype Context = Ctxt IState

> -- | Abstract type representing goal or subgoal names.
> data Goal = Goal Name | DefaultGoal
>     deriving Eq

> instance Show Goal where
>     show (Goal g) = show g
>     show (DefaultGoal) = "Default Goal"

> goal :: String -> Goal
> goal g = Goal $ UN g

> defaultGoal :: Goal
> defaultGoal = DefaultGoal

> -- |A tactic is any function which manipulates a term at the given goal
> -- binding. Tactics may fail, hence the monad.
> type Tactic = Goal -> Context -> TTM Context

> -- | Initialise a context, with no data or definitions and an
> -- empty proof state.
> emptyContext :: Context
> emptyContext = Ctxt initstate

> class IsTerm a where
>     -- | Typecheck a term
>     check :: Context -> a -> TTM Term
>     raw :: a -> TTM Raw

> class IsData a where
>     -- Add a data type with case and elim rules an elimination rule
>     addData :: Context -> a -> TTM Context
>     addData ctxt x = addData' True ctxt x
>     -- Add a data type without an elimination rule
>     addDataNoElim :: Context -> a -> TTM Context
>     addDataNoElim ctxt x = addData' False ctxt x
>     addData' :: Bool -> Context -> a -> TTM Context
