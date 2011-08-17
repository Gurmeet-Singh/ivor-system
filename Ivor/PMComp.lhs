> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.PMComp where

Pattern matching compiler, convert to simple case expressions
(This was originally in Idris, and ideally the Idris version would reuse
this. Let's just make it work first...)

> import Ivor.TTCore
> import Ivor.Values

> import Data.Typeable
> import Debug.Trace
> import Control.Monad.State
> import Data.List hiding (partition)

> data CS = CS Int

> pmcomp :: Gamma Name -> 
>           Name -> TT Name -> PMFun Name -> 
>           ([Name], TSimpleCase Name)
> pmcomp ctxt n ty (PMFun arity ps)
>       = pm' n (map mkPat ps)
>    where mkPat (Sch args _ (Ind rv))
>            = Clause args rv
>          pm' n ps = evalState (doCaseComp ctxt ps) (CS 0)

> data Clause = Clause [Pattern Name] (TT Name)

> isVarPat (Clause ((PVar _):ps) _) = True
> isVarPat (Clause (PTerm:ps) _) = True
> isVarPat _ = False

> isConPat (Clause ((PCon _ _ _ _):ps) _) = True
> isConPat (Clause ((PConst _):ps) _) = True
> isConPat _ = False

> data Partition = Cons [Clause]
>                | Vars [Clause]

> partition :: Gamma Name -> [Clause] -> [Partition]
> partition ctxt [] = []
> partition ctxt ms@(m:_)
>    | isVarPat m = let (vars, rest) = span isVarPat ms in
>                            (Vars vars):partition ctxt rest 
>    | isConPat m = let (cons, rest) = span isConPat ms in
>                            (Cons cons):(partition ctxt rest)
> partition ctxt x = error "Can't happen PMComp partition"

Make sure the variables bound have proper pattern names (to avoid embarrassing
clashes)

> pnames :: [Name] -> TSimpleCase Name -> TSimpleCase Name
> pnames ns (TSCase tm alts) = TSCase (pnamestm ns tm) (map (pnamesalt ns) alts)
> pnames ns (TTm tm) = TTm (pnamestm ns tm)
> pnames ns x = x

> pnamestm :: [Name] -> TT Name -> TT Name
> pnamestm [] tm = tm
> pnamestm (x:xs) tm = substName x (P (PN x)) (Sc (pnamestm xs tm))

> pnamesalt ns (TAlt c t args sc) 
>     = TAlt c t (map PN args) (pnames (ns++args) sc)
> pnamesalt ns (TConstAlt c sc) = TConstAlt c (pnames ns sc)
> pnamesalt ns (TDefault sc) = TDefault (pnames ns sc)

> doCaseComp :: Gamma Name ->
>               [Clause] -> State CS ([Name], TSimpleCase Name)
> doCaseComp ctxt cs = do vs <- newVars cs
>                         let (cs', vs') = reOrder cs vs
>                         sc <- match ctxt (map mkVT vs') cs' TErrorCase
>                         -- return names in original order (this is the
>                         -- argument list we're making)
>                         return (vs, sc)
>    where newVars [] = return []
>          newVars ((Clause ps _):_)
>               = do CS i <- get
>                    put (CS (i+(length ps)))
>                    return $ map (\x-> MN ("cvar", x)) [i..(i+(length ps)-1)]
>          mkVT x = P x

Reorder variables so that one with most disjoint cases is first.
(Actually, quick hack, just reverse them, since then the dependent things
will at least be looked at last, and we'll be matching on the real arguments
rather than indices.)

>          reOrder cs vs = let djs = (reverse.sort.(mapI 0 dj).transpose.allArgs) cs in
>                              (pickAll (map snd djs) cs, pick (map snd djs) vs)
>          pickAll _ [] = []
>          pickAll djs ((Clause args rest):cs) 
>                       = (Clause (pick djs args) rest):(pickAll djs cs)
>          allArgs [] = []
>          allArgs ((Clause args rest):cs) = args:(allArgs cs)

>          pick [] _ = []
>          pick (i:is) xs = if (i<length xs) then xs!!i : (pick is xs)
>                              else error ("ARGH! pick " ++ show i)

Count the number of different constructor forms in xs

>          dj xs = dj' [] xs
>          dj' acc [] = length (nub acc)
>          dj' acc (PCon i _ _ p:xs) = dj' (i:acc) xs
>          dj' acc (_:xs) = dj' acc xs

>          mapI i f [] = []
>          mapI i f (x:xs) = (f x, i):(mapI (i+1) f xs)

> match :: Gamma Name -> 
>          [TT Name] -> -- arguments
>          [Clause] -> -- clauses
>          TSimpleCase Name -> -- fallthrough (error case)
>          State CS (TSimpleCase Name)
> match ctxt [] ((Clause [] ret):_) err 
>           = return $ TTm ret -- run out of arguments
> match ctxt vs cs err 
>       = mixture ctxt vs (partition ctxt cs) err

> mixture :: Gamma Name -> 
>            [TT Name] ->
>            [Partition] -> TSimpleCase Name -> State CS (TSimpleCase Name)
> mixture ctxt vs [] err = return err
> mixture ctxt vs ((Cons ms):ps) err 
>     = do fallthrough <- (mixture ctxt vs ps err)
>          conRule ctxt vs ms fallthrough
> mixture ctxt vs ((Vars ms):ps) err 
>     = do fallthrough <- (mixture ctxt vs ps err)
>          varRule ctxt vs ms fallthrough

In the constructor rule:

For each distinct constructor (or constant) create a group of possible
patterns in ConType and Group

> data ConType = CName Name Int -- ordinary named constructor
>              | forall c. Constant c => CConst c -- constant pattern

> data Group = ConGroup ConType -- constructor
>              -- arguments and rest of alternative for each instance
>                    [([Pattern Name], Clause)] 

> conRule :: Gamma Name -> [TT Name] ->
>            [Clause] -> TSimpleCase Name -> State CS (TSimpleCase Name)
> conRule ctxt (v:vs) cs err = 
>    do groups <- groupCons cs
>       caseGroups ctxt (v:vs) groups err

> caseGroups :: Gamma Name -> [TT Name] ->
>               [Group] -> TSimpleCase Name ->
>               State CS (TSimpleCase Name)
> caseGroups ctxt (v:vs) gs err
>    = do g <- altGroups gs
>         return $ TSCase v g
>   where altGroups [] = return [TDefault err]
>         altGroups ((ConGroup (CName n i) args):cs)
>           = do g <- altGroup n i args
>                rest <- altGroups cs
>                return (g:rest)
>         altGroups ((ConGroup (CConst cval) args):cs)
>           = do g <- altConstGroup cval args
>                rest <- altGroups cs
>                return (g:rest)

>         altGroup n i gs 
>            = do (newArgs, nextCs) <- argsToAlt gs
>                 matchCs <- match ctxt (map P newArgs++vs)
>                                           nextCs err
>                 return $ TAlt n i newArgs matchCs
>         altConstGroup n gs
>            = do (_, nextCs) <- argsToAlt gs
>                 matchCs <- match ctxt vs nextCs err
>                 return $ TConstAlt n matchCs

Find out how many new arguments we need to generate for the next step
of matching (since we're going to be matching further on the arguments
of each group for the constructor, and we'll need to give them names)

Return the new variables we've added to do case analysis on, and the
new set of clauses to match.

> argsToAlt :: [([Pattern Name], Clause)] -> State CS ([Name], [Clause])
> argsToAlt [] = return ([],[])
> argsToAlt rs@((r,m):_) 
>       = do newArgs <- getNewVars r
>            -- generate new match alternatives, by combining the arguments
>            -- matched on the constructor with the rest of the clause
>            return (newArgs, addRs rs)
>     where getNewVars [] = return []
>           getNewVars ((PVar n):ns) = do nsv <- getNewVars ns
>                                         return (n:nsv)
>           getNewVars (_:ns) = do v <- getVar
>                                  nsv <- getNewVars ns
>                                  return (v:nsv)
>           addRs [] = []
>           addRs ((r,(Clause ps res) ):rs)
>               = (Clause (r++ps) res):(addRs rs)

> getVar :: State CS Name
> getVar = do (CS var) <- get
>             put (CS (var+1))
>             return (MN ("pvar", var))

> groupCons :: Monad m => [Clause] -> m [Group]
> groupCons cs = gc [] cs
>    where gc acc [] = return acc
>          gc acc ((Clause (p:ps) res):cs) = do
>            acc' <- addGroup p ps res acc
>            gc acc' cs

>          addGroup p ps res acc = case p of
>             PCon i con _ args -> return $ addg con i args (Clause ps res) acc
>             PConst cval -> return $ addConG cval (Clause ps res) acc
>             pat -> fail $ show pat ++ " is not a constructor or constant (can't happen)"
          
>          addg con i conargs res [] 
>                   = [ConGroup (CName con i) [(conargs, res)]]
>          addg con i conargs res (g@(ConGroup (CName n j) cs):gs)
>               | i == j = (ConGroup (CName n i) (cs ++ [(conargs, res)])):gs
>               | otherwise = g:(addg con i conargs res gs)

>          addConG :: Constant c => c -> Clause -> [Group] -> [Group]
>          addConG con res [] = [ConGroup (CConst con) [([],res)]]
>          addConG con res (g@(ConGroup (CConst n) cs):gs)
>               | constEq con n = (ConGroup (CConst n) (cs ++ [([], res)])):gs
>               | otherwise = g:(addConG con res gs)

HATEHATEHATE. This completely defeats the point of having generic constants.
However, it seems there is no alternative... pattern matching will only work
for Int, String and Char as a result.

> constEq :: (Constant a, Constant b) => a -> b -> Bool
> constEq x y = ceq_1 (cast x) (cast y)
>               || ceq_2 (cast x) (cast y)
>               || ceq_3 (cast x) (cast y)
>    where ceq_1 :: Maybe Int -> Maybe Int -> Bool
>          ceq_1 (Just x) (Just y) = x == y
>          ceq_1 _ _ = False
>          ceq_2 :: Maybe String -> Maybe String -> Bool
>          ceq_2 (Just x) (Just y) = x == y
>          ceq_2 _ _ = False
>          ceq_3 :: Maybe Char -> Maybe Char -> Bool
>          ceq_3 (Just x) (Just y) = x == y
>          ceq_3 _ _ = False


In the variable rule:

case v args of
   p pats -> r1
   ...
   pn patsn -> rn

====>

case args of
   pats -> r1[p/v]
   ...
   patsn -> rn[p/v]

> varRule :: Gamma Name -> [TT Name] ->
>            [Clause] -> TSimpleCase Name -> State CS (TSimpleCase Name)
> varRule ctxt (v:vs) alts err = do
>     let alts' = map (repVar v) alts
>     match ctxt vs alts' err
>   where repVar v (Clause ((PVar p):ps) res) 
>                    = let nres = substName p v (Sc res) in
>                      {- trace (show v ++ " for " ++ dbgshow p ++ " in " ++ show res ++ " gives " ++ show nres) $ -}
>                          Clause ps nres
>         repVar v (Clause (PTerm:ps) res) = Clause ps res

