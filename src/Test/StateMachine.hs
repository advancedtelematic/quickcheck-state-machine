{-# LANGUAGE GADTs      #-}
{-# LANGUAGE Rank2Types #-}

module Test.StateMachine
  ( sequentialProperty
  , parallelProperty
  ) where

import           Control.Monad.State                   (evalStateT, replicateM_)
import qualified Data.Map                              as M
import           Data.Singletons.TH                    (DemoteRep, SDecide,
                                                        SingKind)
import           Test.QuickCheck                       (Gen)
import           Test.QuickCheck.Monadic               (monadic, monadicIO, run)
import           Test.QuickCheck.Property              (Property)

import qualified Test.StateMachine.Internal.IxMap      as IxM
import           Test.StateMachine.Internal.Parallel
import           Test.StateMachine.Internal.Sequential
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Types
import           Test.StateMachine.Internal.Utils

------------------------------------------------------------------------

sequentialProperty
  :: Monad m
  => ShowCmd cmd
  => IxTraversable cmd
  => HasResponse cmd
  => Ord       ix
  => SDecide   ix
  => SingKind  ix
  => DemoteRep ix ~ ix
  => StateMachineModel model cmd
  -> Gen (Untyped cmd (RefPlaceholder ix))
  -> (forall resp refs'. Shrinker (cmd refs' resp))
  -> (forall resp. cmd refs resp -> m (Response_ refs resp))
  -> (m Property -> Property)
  -> Property
sequentialProperty smm gens shrinker sem runM =
  forAllShrinkShow
    (fst <$> liftGen gens 0 M.empty)
    (liftShrink shrinker)
    showIntRefedList
    $ \cmds -> collectStats cmds $
        monadic (runM . flip evalStateT IxM.empty) $
          checkSequentialInvariant smm (initialModel smm) sem cmds

------------------------------------------------------------------------

parallelProperty
  :: Ord       ix
  => SDecide   ix
  => SingKind  ix
  => DemoteRep ix ~ ix
  => ShowCmd        cmd
  => IxTraversable  cmd
  => HasResponse    cmd
  => StateMachineModel model cmd
  -> Gen (Untyped cmd (RefPlaceholder ix))
  -> (forall resp refs'. Shrinker (cmd refs' resp))
  -> (forall resp. cmd refs resp -> IO (Response_ refs resp))
  -> Property
parallelProperty smm gen shrinker sem
  = forAllShrinkShow
      (liftGenFork gen)
      (liftShrinkFork shrinker)
      (showFork showIntRefedList)
      $ \fork -> monadicIO $ replicateM_ 10 $ do
          hist <- run $ liftSemFork sem fork
          checkParallelInvariant smm hist
