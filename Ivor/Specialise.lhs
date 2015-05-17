> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.Specialise where

> import Ivor.Gadgets
> import Ivor.TTCore
> import Ivor.Nobby
> import Ivor.Typecheck
> import Ivor.Errors
> import Ivor.Values
> import Ivor.Evaluator

> import Debug.Trace
> import Data.List
> import Control.Monad

Specialise pattern matching definitions

 specialise :: Context -> Patterns ->
               [(Name, ([Int], Int))] -> -- functions with static args
               [Name] -> -- frozen names
               (Patterns, Context, [Name]) -- also, new names
 specialise ctxt p = (p, ctxt, []) -- TODO
