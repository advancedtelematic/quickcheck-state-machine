{-# LANGUAGE DeriveFunctor #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.BoxDrawer
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Mats Daniel Gustafsson <daniel@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains functions for visualing a history of a parallel
-- execution.
--
-----------------------------------------------------------------------------

module Test.StateMachine.BoxDrawer
  ( EventType(..)
  , Fork(..)
  , exec
  ) where

import           Prelude
import           Text.PrettyPrint.ANSI.Leijen
                   (Doc, text, vsep)

import           Test.StateMachine.Types
                   (Pid(..))

------------------------------------------------------------------------

-- | Event invocation or response.
data EventType = Open | Close
  deriving (Show)

data Event = Event EventType Pid String

data Cmd = Top | Start String | Active | Deactive | Ret String | Bottom

compile :: [Event] -> ([Cmd], [Cmd])
compile = go (Deactive, Deactive)
  where
    infixr 9 `add`
    add :: (a,b) -> ([a], [b]) -> ([a], [b])
    add (x,y) (xs, ys) = (x:xs, y:ys)

    set :: (a, a) -> Pid -> a -> (a, a)
    set (_x, y) (Pid 1) x' = (x', y)
    set (x, _y) (Pid 2) y' = (x, y')
    set _ pid _      = error $ "compile.set: unknown pid " ++ show pid

    go :: (Cmd, Cmd) -> [Event] -> ([Cmd], [Cmd])
    go _ [] = ([], [])
    go st (Event Open pid l :  rest) =
      set st pid Top `add` set st pid (Start l) `add` go (set st pid Active) rest
    go st (Event Close pid l :  rest) =
      set st pid (Ret l) `add` set st pid Bottom `add` go (set st pid Deactive) rest

size :: Cmd -> Int
size Top       = 4
size (Start l) = 6 + length l
size Active    = 2
size Deactive  = 0
size (Ret l)   = 4 + length l
size Bottom    = 4

adjust :: Int -> Cmd -> String
adjust n Top = "┌" ++ replicate (n - 4) '─' ++ "┐"
adjust n (Start l) = "│ " ++ l ++ replicate (n - length l - 6) ' ' ++ " │"
adjust n Active = "│" ++ replicate (n - 4) ' ' ++ "│"
adjust n Deactive = replicate (n - 2) ' '
adjust n (Ret l) = "│ " ++ replicate (n - 8 - length l) ' ' ++ "→ " ++ l ++ " │"
adjust n Bottom = "└" ++ replicate (n - 4) '─' ++ "┘"

next :: ([Cmd], [Cmd]) -> [String]
next (left, right) = take (length left `max` length right) $ zipWith merge left' right'
  where
    left' = map (adjust $ maximum $ 0:map size left) (left ++ repeat Deactive)
    right' = map (adjust $ maximum $ 0:map size right) (right ++ repeat Deactive)
    merge x y = x ++ " │ " ++ y

toEvent :: [(EventType, Pid)] -> ([String], [String]) -> [Event]
toEvent [] ([], [])             = []
toEvent [] ps = error $ "toEvent: residue inputs: " ++ show ps
toEvent ((e , Pid 1):evT)  (x:xs, ys)   = Event e (Pid 1) x : toEvent evT (xs, ys)
toEvent ((_e, Pid 1):_evT) ([]  , _ys)  = error "toEvent: no input from pid 1"
toEvent ((e , Pid 2):evT)  (xs  , y:ys) = Event e (Pid 2) y : toEvent evT (xs, ys)
toEvent ((_e, Pid 2):_evT) (_xs , [])   = error "toEvent: no input from pid 2"
toEvent (e : _) _ = error $ "toEvent: unknown pid " ++ show e

compilePrefix :: [String] -> [Cmd]
compilePrefix [] = []
compilePrefix (cmd:res:prefix) = Top : Start cmd : Ret res : Bottom : compilePrefix prefix
compilePrefix [cmd] = error $ "compilePrefix: doesn't have response for cmd: " ++ cmd

data Fork a = Fork a a a
  deriving Functor

-- | Given a history, and output from processes generate Doc with boxes
exec :: [(EventType, Pid)] -> Fork [String] -> Doc
exec evT (Fork lops pops rops) = vsep $ map text (preBoxes ++ parBoxes)
  where
    preBoxes = map (adjust $ maximum $ 0:map ((2+) . length) (take 1 parBoxes)) $ compilePrefix pops
    parBoxes = next . compile $ toEvent evT (lops, rops)
