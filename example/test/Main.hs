module Main (main) where

import           Test.Hspec
                   (hspec, parallel)

import           Spec
                   (spec)

------------------------------------------------------------------------

main :: IO ()
main = hspec (parallel spec)
