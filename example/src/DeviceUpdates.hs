{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module DeviceUpdates where

import           Control.Monad.Trans
                   (lift)
import           Data.Constraint
                   ((:-))
import           Data.Map
                   (Map)
import qualified Data.Map                         as M
import           Data.Set
                   (Set)
import qualified Data.Set                         as S
import           Data.Singletons.TH
                   (genSingletons, singDecideInstances)
import           Test.QuickCheck
                   (Arbitrary, Gen, arbitrary, frequency, ioProperty,
                   (===))

import           Test.StateMachine
import           Test.StateMachine.Internal.Types

------------------------------------------------------------------------

data Action :: Signature Refs where

  -- Server
  AddDevice      :: Action refs ('Reference 'DeviceRef)
  AddUpdate      :: Update -> Action refs ('Reference 'UpdateRef)
  ScheduleUpdate :: refs @@ 'UpdateRef -> refs @@ 'DeviceRef -> Action refs ('Response ())
  UpdateReports  :: refs @@ 'DeviceRef -> Action refs ('Response (Set Update))

  -- Device
  PullUpdates    :: refs @@ 'DeviceRef -> Action refs ('Response ())

  -- Device operator
  ViewUpdates    :: refs @@ 'DeviceRef -> Action refs ('Response (Set Update))

data Refs = DeviceRef | UpdateRef
  deriving (Eq, Ord)

data Update = Update String
  deriving (Eq, Ord, Show)

instance Arbitrary Update where
  arbitrary = Update <$> arbitrary

$(genSingletons       [''Refs])
$(singDecideInstances [''Refs])

------------------------------------------------------------------------

data Model refs = Model
  { installedUpdates :: Map (refs @@ 'DeviceRef) (Set Update)
  , pendingUpdates   :: Map (refs @@ 'DeviceRef) (Set Update)
  , updates          :: Map (refs @@ 'UpdateRef) Update
  }

instance IxForallF Show refs => Show (Model refs) where
  show m = concat
    [ "Model\n  { installedUpdates = "
    , show (installedUpdates m)
    , "\n  , ", "pendingUpdates   = "
    , show (pendingUpdates m)
    , "\n  , ", "updates          = "
    , show (updates m)
    , "\n  }"
    ]
    \\ (iinstF @'DeviceRef Proxy :: IxForallF Show refs :- Show (refs @@ 'DeviceRef))
    \\ (iinstF @'UpdateRef Proxy :: IxForallF Show refs :- Show (refs @@ 'UpdateRef))

initModel :: Model ref
initModel = Model M.empty M.empty M.empty

preconditions
  :: forall refs resp. IxForallF Ord refs
  => Model refs -> Action refs resp -> Bool
preconditions m cmd = (case cmd of
  AddDevice                -> True
  AddUpdate _              -> True
  ScheduleUpdate uref dref ->
    uref `elem` M.keys (updates m) &&
    dref `elem` M.keys (installedUpdates m)
  UpdateReports dref       -> dref `elem` M.keys (installedUpdates m)
  PullUpdates dref         -> dref `elem` M.keys (installedUpdates m)
  ViewUpdates dref         -> dref `elem` M.keys (installedUpdates m)
  ) \\ (iinstF @'DeviceRef Proxy :: Ords' refs 'DeviceRef)
    \\ (iinstF @'UpdateRef Proxy :: Ords' refs 'UpdateRef)

transitions
  :: forall refs resp. IxForallF Ord refs
  => Model refs -> Action refs resp -> Response_ refs resp -> Model refs
transitions m cmd resp = (case cmd of

  AddDevice                ->
    m { installedUpdates = M.insert resp S.empty (installedUpdates m)
      , pendingUpdates   = M.insert resp S.empty (pendingUpdates   m)
      }

  AddUpdate update         ->
    m { updates = M.insert resp update (updates m) }

  ScheduleUpdate uref dref ->
    let update = S.singleton (updates m M.! uref) in
    m { pendingUpdates   = M.insertWith S.union dref update (pendingUpdates m) }

  UpdateReports _          -> m

  PullUpdates dref         ->
    m { installedUpdates = M.insertWith S.union dref (pendingUpdates m M.! dref)
                                                     (installedUpdates m)
      , pendingUpdates   = M.insert dref S.empty (pendingUpdates m)
      }

  ViewUpdates _            -> m

  ) \\ (iinstF @'DeviceRef Proxy :: Ords' refs 'DeviceRef)
    \\ (iinstF @'UpdateRef Proxy :: Ords' refs 'UpdateRef)

postconditions
  :: forall refs resp. IxForallF Ord refs
  => Model refs -> Action refs resp -> Response_ refs resp -> Property
postconditions m cmd resp = (case cmd of
  ViewUpdates   dref -> resp === installedUpdates m M.! dref
  UpdateReports dref -> resp === installedUpdates m M.! dref
  PullUpdates   dref -> pendingUpdates m' M.! dref === S.empty
  _                  -> property True
  ) \\ (iinstF @'DeviceRef Proxy :: Ords' refs 'DeviceRef)
  where
  m' = transitions m cmd resp

smm :: StateMachineModel Model Action
smm = StateMachineModel preconditions postconditions transitions initModel

------------------------------------------------------------------------

gen :: Gen (Untyped Action (RefPlaceholder Refs))
gen = frequency
  [ (1, return . Untyped $ AddDevice)
  , (5, Untyped . AddUpdate <$> arbitrary)
  , (5, return . Untyped $ ScheduleUpdate SUpdateRef SDeviceRef)
  , (5, return . Untyped $ UpdateReports SDeviceRef)
  , (5, return . Untyped $ PullUpdates SDeviceRef)
  , (5, return . Untyped $ ViewUpdates SDeviceRef)
  ]

shrink1 :: Action refs resp -> [Action refs resp]
shrink1 _ = []

------------------------------------------------------------------------

debugSemantics
  :: Model ConstIntRef -> MayResponse_ ConstIntRef resp -> Action ConstIntRef resp
  -> IO (Response_ ConstIntRef resp)
debugSemantics m miref cmd = case cmd of
  AddDevice           -> return miref
  AddUpdate _         -> return miref
  ScheduleUpdate _ _  -> return ()
  UpdateReports  dref -> return (installedUpdates m M.! dref)
  PullUpdates    _    -> return ()
  ViewUpdates    dref -> return (installedUpdates m M.! dref)

------------------------------------------------------------------------

instance ShowCmd Action where
  showCmd  AddDevice                 = "AddDevice"
  showCmd (AddUpdate update)         = "AddUpdate ("      ++ show update ++ ")"
  showCmd (ScheduleUpdate uref dref) = "ScheduleUpdate " ++ uref ++
                                         " " ++ dref ++ ""
  showCmd (UpdateReports  dref)      = "UpdateReports "  ++ dref
  showCmd (PullUpdates    dref)      = "PullUpdates "    ++ dref
  showCmd (ViewUpdates    dref)      = "ViewUpdates "    ++ dref

instance HasResponse Action where
  response AddDevice         = SReference SDeviceRef
  response AddUpdate      {} = SReference SUpdateRef
  response ScheduleUpdate {} = SResponse
  response UpdateReports  {} = SResponse
  response PullUpdates    {} = SResponse
  response ViewUpdates    {} = SResponse

instance IxFunctor Action where
  ifmap _  AddDevice                 = AddDevice
  ifmap _ (AddUpdate update)         = AddUpdate update
  ifmap f (ScheduleUpdate uref dref) = ScheduleUpdate (f SUpdateRef uref)
                                                      (f SDeviceRef dref)
  ifmap f (UpdateReports  dref)      = UpdateReports  (f SDeviceRef dref)
  ifmap f (PullUpdates    dref)      = PullUpdates    (f SDeviceRef dref)
  ifmap f (ViewUpdates    dref)      = ViewUpdates    (f SDeviceRef dref)

instance IxFoldable Action where
  ifoldMap _  AddDevice                 = mempty
  ifoldMap _ (AddUpdate _)              = mempty
  ifoldMap f (ScheduleUpdate uref dref) = f SUpdateRef uref `mappend`
                                          f SDeviceRef dref
  ifoldMap f (UpdateReports  dref)      = f SDeviceRef dref
  ifoldMap f (PullUpdates    dref)      = f SDeviceRef dref
  ifoldMap f (ViewUpdates    dref)      = f SDeviceRef dref

instance IxTraversable Action where
  itraverse _ _  AddDevice                 = pure AddDevice
  itraverse _ _ (AddUpdate update)         = pure (AddUpdate update)
  itraverse _ f (ScheduleUpdate uref dref) = ScheduleUpdate <$> f SUpdateRef uref
                                                            <*> f SDeviceRef dref
  itraverse _ f (UpdateReports  dref)      = UpdateReports  <$> f SDeviceRef dref
  itraverse _ f (PullUpdates    dref)      = PullUpdates    <$> f SDeviceRef dref
  itraverse _ f (ViewUpdates    dref)      = ViewUpdates    <$> f SDeviceRef dref

------------------------------------------------------------------------

prop_sequential :: Property
prop_sequential = sequentialProperty'
  smm
  (lift gen)
  ()
  shrink1
  debugSemantics
  ioProperty
