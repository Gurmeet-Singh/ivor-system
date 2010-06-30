> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.Evaluator(eval_whnf, eval_nf, eval_nf_env,
>                       eval_nf_without, eval_nf_limit,
>                       eval_nfEnv, tidyNames) where

> import Ivor.TTCore
> import Ivor.Gadgets
> import Ivor.Constant
> import Ivor.Values

> import Debug.Trace
> import Data.Typeable
> import Control.Monad.State
> import List
> import qualified Data.Map as Map

 data Machine = Machine { term :: (TT Name),
                          mstack :: [TT Name],
                          menv :: [(Name, Binder (TT Name))] }

> eval_whnf :: Gamma Name -> Indexed Name -> Indexed Name
> eval_whnf gam (Ind tm) = let res = makePs (evaluate False gam tm Nothing Nothing Nothing)
>                              in finalise (Ind res)

> eval_nf :: Gamma Name -> Indexed Name -> Indexed Name
> eval_nf gam (Ind tm) = let res = makePs (evaluate True gam tm Nothing Nothing Nothing)
>                            in finalise (Ind res)

> eval_nf_env :: Env Name -> Gamma Name -> Indexed Name -> Indexed Name
> eval_nf_env env g t
>     = eval_nf (addenv env g) t
>   where addenv [] g = g
>         addenv ((n,B (Let v) ty):xs) (Gam g)
>             = addenv xs (Gam (Map.insert n (G (Fun [] (Ind v)) (Ind ty) defplicit) g))
>         addenv (_:xs) g = addenv xs g

> eval_nf_without :: Gamma Name -> Indexed Name -> [Name] -> Indexed Name
> eval_nf_without gam tm [] = eval_nf gam tm
> eval_nf_without gam (Ind tm) ns = let res = makePs (evaluate True gam tm (Just ns) Nothing Nothing)
>                                       in finalise (Ind res)

> eval_nf_limit :: Gamma Name -> Indexed Name -> [(Name, Int)] -> 
>                  Maybe [(Name, ([Int], Int))] -> Indexed Name
> eval_nf_limit gam tm [] stat = eval_nf gam tm
> eval_nf_limit gam (Ind tm) ns stat 
>     = -- trace (show (tm, stat)) $
>       let res = makePs (evaluate True gam tm Nothing (Just ns) stat)
>           in finalise (Ind res)

> type SEnv = [(Name, TT Name, TT Name)]
> type Stack = [(TT Name, SEnv, [(Name, TT Name)])]

> getEnv i env = (\ (_,_,val) -> val) (traceIndex env i "Evaluator fail")
> sfst (n,_,_) = n
> senv (_,e,_) = e
> stkpats (_,_,p) = p

> allNames :: Stack -> SEnv -> [(Name, TT Name)] -> [Name]
> allNames stk env pats = map sfst env ++ map fst pats ++
>                         concat (map (map sfst) (map senv stk)) ++
>                         concat (map (map fst) (map stkpats stk))

Code			Stack	Env	Result

[[x{global}]]		xs	es	(lookup x), xs, es
[[x{local}]]		xs	es	(es!!x), xs, es
[[f a]]			xs	es	[[f]], a:xs, es
[[\x . e]]		(x:xs)	es	[[e]], xs, (x:es)
[[\x . e]]		[]	es	\x . [[e]], xs, (Lam x: es)
(or leave alone for whnf)
[[let x = t in e]]	xs	es	[[e]], xs, (Let x t: es)

> type EvalState = (Maybe [(Name, Int)], 
>                   Maybe [(Name, ([Int], Int))])

> evaluate :: Bool -> -- under binders? 'False' gives WHNF
>             Gamma Name -> TT Name -> 
>             Maybe [Name] ->  -- Names not to reduce
>             Maybe [(Name, Int)] -> -- Names to reduce a maximum number
>             Maybe [(Name, ([Int], Int))] -> -- Names and list of static args
>             TT Name
> evaluate open gam tm jns maxns statics = -- trace ("EVALUATING: " ++ debugTT tm) $ 
>                                  let res = evalState (eval (True, True) tm [] [] []) (maxns, statics)
>                                      in {- trace ("RESULT: " ++ debugTT res) -}
>                                         res
>   where
>     eval :: (Bool, Bool) -> TT Name -> Stack -> SEnv -> 
>             [(Name, TT Name)] -> State EvalState (TT Name)
>     eval nms tm stk env pats = {- trace (show (tm, stk, env, pats)) $ -} eval' nms tm stk env pats

>     eval' (everything, top) (P x) xs env pats 
>         = do (mns, sts) <- get
>              let (use, mns', sts') = 
>                      if (everything || top)
>                         then usename x jns mns (sts, (xs, pats))
>                         else (False, mns, sts)
>              put (mns', sts)
>              -- when (not nms) (trace ("Not using " ++ show x) (return ()))
>              case lookup x pats of
>                 Nothing -> if use && (everything || top)
>                                 then evalP (everything, top) x (lookupval x gam) xs env pats
>                                 else evalP (everything, top) x Nothing xs env pats
>                 Just val -> eval (everything, False) val xs env (removep x pats)
>        where removep n [] = []
>              removep n ((x,t):xs) | n==x = removep n xs
>                                   | otherwise = (x,t):(removep n xs)
>     eval' nms@(ev,_) (V i) xs env pats 
>              = if (length env>i) 
>                   then eval nms (getEnv i env) xs env pats
>                   else unload ev (V i) xs pats env -- blocked, so unload
>     eval' nms (App f a) xs env pats 
>        = do -- a' <- eval a [] env pats
>             eval nms f ((a, env, pats):xs) env pats
>     eval' nms (Bind n (B Lambda ty) (Sc sc)) xs env pats
>        = do ty' <- eval nms ty [] env pats
>             evalScope nms Lambda n ty' sc xs env pats
>     eval' nms (Bind n (B Pi ty) (Sc sc)) xs env pats
>        = do ty' <- eval nms ty [] env pats
>             evalScope nms Pi n ty' sc xs env pats
>            -- unload (Bind n (B Pi ty') (Sc sc)) [] pats env
>     eval' nms (Bind n (B (Let val) ty) (Sc sc)) xs env pats 
>        = do val' <- eval nms val [] env pats
>             ty' <- eval nms ty [] env pats
>             eval nms sc xs ((n,ty',val'):env) pats
>     eval' nms@(ev,_) (Bind n (B bt ty) (Sc sc)) xs env pats
>        = do ty' <- eval nms ty [] env pats
>             unload ev (Bind n (B bt ty') (Sc sc)) [] pats env
>     eval' (ev,_) x stk env pats = unload ev x stk pats env

>     evalP (ev, top) n (Just v) xs env pats 
>        = case v of
>             Fun opts (Ind v) -> eval (ev, False) v xs env pats
>             PatternDef p _ _ -> pmatch (ev, top) n p xs env pats
>             PrimOp _ f -> do xs' <- mapM (\(x, xenv, xpats) -> eval (ev, False) x [] xenv xpats) xs
>                              case f xs' of
>                                Nothing -> unload ev (P n) xs pats env
>                                Just v -> eval (ev, False) v [] env pats
>             _ -> unload ev (P n) xs pats env
>     evalP (ev,top) n Nothing xs env pats = unload ev (P n) xs pats env -- blocked, so unload stack

>     evalScope nms b n ty sc stk@((x,xenv,xpats):xs) env pats 
>              = do let n' = uniqify' n (allNames stk env pats)
>                   x' <- eval nms x [] xenv xpats
>                   eval nms sc xs ((n',ty,x'):env) pats
>     evalScope nms@(ev,_) b n ty sc [] env pats
>       | open = do let n' = uniqify' n (allNames [] env pats)
>                   let tmpname = uniqify' (MN ("E", length env)) (allNames [] env pats) -- (MN ("E", length env))
>                   sc' <- eval nms sc [] ((n',ty,P tmpname):env) pats
>                   let newsc = pToV tmpname sc'
>                   u' <- unload ev (Bind n' (B b ty) newsc) [] pats env
>                   return $ buildenv env u'
>       | otherwise 
>          = do let n' = uniqify' n (allNames [] env pats)
>               u' <-  unload ev (Bind n' (B Lambda ty) (Sc sc)) [] pats env -- in Whnf
>               return $ buildenv env u'
>     unload ev x [] pats env 
>                = return $ foldl (\tm (n,val) -> substName n val (Sc tm)) x pats
>     unload ev x ((a, aenv, apats):as) pats env 
>                = do a' <- eval (ev, False) a [] aenv apats
>                     unload ev (App x a') as pats env
>
>     uniqify' u@(UN n) ns = uniqify (MN (n,0)) ns
>     uniqify' n ns = uniqify n ns

     usename x _ mns (sts, (stk, pats)) 
          | Just (static, arity) <- lookup x sts 
              = useDyn x mns static arity stk pats

>     usename x Nothing Nothing (sts, _) = (True, Nothing, sts)
>     usename x _ (Just ys) (sts, _) 
>                 = case lookup x ys of
>                      Just 0 -> (False, Just ys, sts)
>                      Just n -> (True, Just (update x (n-1) ys), sts)
>                      _ -> (True, Just ys, sts)
>     usename x (Just xs) m (sts, _) = (not (elem x xs), m, sts)

     useDyn x mns static arity stk pats =

>     update x v [] = []
>     update x v ((k,_):xs) | x == k = ((x,v):xs)
>     update x v (kv:xs) = kv : update x v xs

>     buildenv [] t = t
>     buildenv ((n,ty,tm):xs) t 
>                 = buildenv xs (subst tm (Sc t))
>     --            = buildenv xs (Bind n (B (Let tm) ty) (Sc t))

>     renameRHS pbinds rhs env stk = rrhs [] [] (nub pbinds) rhs where
>       rrhs namemap pbinds' [] rhs = {-trace ("BEFORE " ++ show (rhs, pbinds, pbinds')) $ -}
>                                     (pbinds', substNames namemap rhs)
>       rrhs namemap pbinds ((n,t):ns) rhs
>          = let n' = uniqify' (UN (show n)) (map sfst env ++ 
>                                             map fst pbinds ++ map fst ns ++ 
>                                             concat (map (map sfst) (map senv stk)) ++ 
>                                             concat (map (map fst) (map stkpats stk))) in
>                rrhs ((n,P n'):namemap) ((n',t):pbinds) ns rhs

>     substNames [] rhs = {-trace ("AFTER " ++ show rhs) $ -} rhs
>     substNames ((n,t):ns) rhs = substNames ns (substName n t (Sc rhs))

>     pmatch (False, False) n _ xs env pats 
>            = unload False (P n) xs pats env
>     pmatch (ev, top) n (PMFun i clauses) xs env pats = matchtrace (show n) xs $ 
>         do (mns, statics) <- get
>            let static = fmap (lookup n) statics
>            let rcs = reqCons clauses
>            {- xs' <- zipWithM (\(x, xenv, xpats) reqcon -> 
>                     do x' <- if reqcon then eval (False, True) x [] xenv pats
>                                        else return x     
>                        return (x', xenv, xpats)) xs rcs -}
>            old <- get -- HACK! If it fails, restore old state
>            cm <- matches clauses xs env pats
>            case cm of
>              Nothing -> do put old
>                            unload ev (P n) xs pats env
>              Just (rhs, pbinds, stk) -> 
>                    let rhsin = case static of
>                                  Nothing -> rhs
>                                  Just foo -> {- trace (show (n, foo)) $ -} rhs 
>                        (pbinds', rhs') = renameRHS pbinds rhsin env xs in
>                        rhstrace (show n) rhs' pbinds'
>                           $ eval (ev, False) rhs' stk env pbinds'

>     reqCons [] = repeat False
>     reqCons ((Sch pats _ _):ss) = zipWith (||) (reqCons ss) (rc pats)
>     rc [] = []
>     rc ((PCon _ _ _ _):ps) = True:(rc ps)
>     rc ((PConst _):ps) = True:(rc ps)
>     rc (_:ps) = False:(rc ps)

>     matches [] xs env pats = return Nothing
>     matches (c:cs) xs env pats 
>        = do cm <- (match c xs env pats)
>             case cm of
>               Just v -> return $ Just v
>               Nothing -> matches cs xs env pats

>     match :: Scheme Name -> Stack -> SEnv -> 
>              [(Name, TT Name)] ->
>              State EvalState (Maybe (TT Name, [(Name, TT Name)], Stack))
>     match (Sch pats _ rhs) xs env patvars 
>               = matchargs pats xs rhs env patvars []
>     matchargs [] xs (Ind rhs) env patvars pv' = return $ Just (rhs, pv', xs)
>     matchargs (p:ps) ((x, xenv, xpats):xs) rhs env patvars pv'
>       = do old <- get
>            x' <- {- trace ("against " ++ show x) $ -} eval (False, True) x [] xenv xpats
>            xm <-  matchPat p x' xenv xpats pv' old
>            case xm of
>              Just patvars' -> matchargs ps xs rhs env patvars patvars'
>              Nothing -> do put old
>                            return Nothing

                do xnms' <- eval True x [] xenv xpats
                   trace ("Fully evalled " ++ show (x,xnms')) $ case matchPat p x' pv' of
                     Just patvars' -> matchargs ps xs rhs env patvars patvars'
                     Nothing -> return Nothing

>     matchargs _ _ _ _ _ _ = return Nothing

>     matchPat PTerm x _ _ patvars old = return $ Just patvars
>     matchPat (PVar n) x _ _ patvars old
>         = return $ Just ((n,x):patvars) -- (filter (\ (x,y) -> x/=n) patvars))
>     matchPat (PConst t) x xenv xpats patvars old
>              = do x' <- eval (True, True) x [] [] []
>                   case x' of
>                     Const t' -> case cast t of
>                                   Just tc -> 
>                                      if (tc == t') then return $ Just patvars
>                                                    else return Nothing
>                     _ -> return Nothing
>     matchPat pc@(PCon t _ _ args) x xenv xpats patvars old
>              = do -- old <- get
>                   x' <- eval (False, True) x [] xenv xpats
>                   case getConArgs x' [] of
>                     Just (tag, cargs) ->
>                        if (tag == t) then matchPats args cargs patvars
>                                      else return Nothing
>                     _ -> do put old
>                             x' <- eval (True, True) x [] xenv xpats
>                             case getConArgs x' [] of
>                               Just (tag, cargs) ->
>                                 if (tag == t) then matchPats args cargs patvars
>                                               else return Nothing

>                               _ -> return Nothing
>         where matchPats [] [] patvars = return $ Just patvars
>               matchPats (a:as) (b:bs) patvars
>                   = do vs' <- matchPat a b xenv xpats patvars old
>                        case vs' of
>                          Just pats -> matchPats as bs pats
>                          Nothing -> return Nothing
>               matchPats _ _ _ = return Nothing
>     matchPat _ _ _ _ _ _ = return Nothing

>     getConArgs (Con t _ _) args = Just (t, args)
>     getConArgs (App f a) args = getConArgs f (a:args)
>     getConArgs _ _ = Nothing



> eval_nfEnv :: Env Name -> Gamma Name -> Indexed Name -> Indexed Name
> eval_nfEnv env g t
>     = eval_nf (addenv env g) t
>   where addenv [] g = g
>         addenv ((n,B (Let v) ty):xs) (Gam g)
>             = addenv xs (Gam (Map.insert n (G (Fun [] (Ind v)) (Ind ty) defplicit) g))
>         addenv (_:xs) g = addenv xs g

Turn MN to UN, if they are unique, so that they look nicer.

> tidyNames :: Indexed Name -> Indexed Name
> tidyNames (Ind tm) = Ind (tidy' [] tm)
>   where tidy' ns (Bind (MN (n,i)) (B b t) (Sc tm)) = 
>             let n' = uniqify (UN n) ns in
>                 Bind n' (B b (tidy' ns t)) (Sc (tidy' (n':ns) tm))
>         tidy' ns (Bind x (B b t) (Sc tm)) 
>               = Bind x (B b (tidy' ns t)) (Sc (tidy' (x:ns) tm))
>         tidy' ns (App f a) = App (tidy' ns f) (tidy' ns a)
>         tidy' ns x = x

Various tracing facilities for spying on specific cases

> tracefns = []

> matchtrace n xs =
>    if (n `elem` tracefns)
>        then trace ("Matching " ++ n ++ " " ++ show (map (\(x,y,z) -> x) xs))
>        else id

> rhstrace n rhs pbinds =
>    if (n `elem` tracefns)
>       then trace ("Returned " ++ n ++ " => " ++ show rhs ++ "\n" ++
>                               showb pbinds)
>       else id
>   where showb [] = ""
>         showb (m:xs) = "  " ++ show m ++ "\n" ++ showb xs