{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Spec where

import Control.Applicative
import Control.Exception
import Control.Monad.Reader
import Data.Either
import Data.Function
import Data.List
import Data.List qualified as L
import Data.Map (Map)
import Data.Map qualified as Map
import Etna.Lib
import GHC.Conc
import Impl
import StateModel
import StateModel.Variables
import Test.QuickCheck
import Test.QuickCheck.Monadic hiding (assert)
import Test.QuickCheck.Monadic qualified as QC

data RegState = RegState
  { regs :: Map String (Var ThreadId),
    dead :: [Var ThreadId]
  }
  deriving (Show, Generic)

deriving instance Show (Action RegState a)

deriving instance Eq (Action RegState a)

instance HasVariables (Action RegState a) where
  getAllVariables (Register _ v) = getAllVariables v
  getAllVariables (KillThread v) = getAllVariables v
  getAllVariables _ = mempty

instance StateModel RegState where
  data Action RegState a where
    Spawn :: Action RegState ThreadId
    WhereIs :: String -> Action RegState (Maybe ThreadId)
    Register :: String -> Var ThreadId -> Action RegState (Either SomeException ())
    Unregister :: String -> Action RegState (Either SomeException ())
    KillThread :: Var ThreadId -> Action RegState ()

  precondition s (Register name tid) =
    name `Map.notMember` regs s
      && tid `notElem` Map.elems (regs s)
      && tid `notElem` dead s
  precondition s (Unregister name) =
    name `Map.member` regs s
  precondition _ _ = True

  validFailingAction _ _ = True

  arbitraryAction ctx s =
    frequency $
      [ ( max 1 $ 10 - length (ctxAtType @ThreadId ctx),
          return $ Some Spawn
        ),
        ( 2 * Map.size (regs s),
          Some <$> (Unregister <$> probablyRegistered s)
        ),
        ( 10,
          Some <$> (WhereIs <$> probablyRegistered s)
        )
      ]
        ++ [ ( max 1 $ 3 - length (dead s),
               Some <$> (KillThread <$> arbitraryVar ctx)
             )
             | not . null $ ctxAtType @ThreadId ctx
           ]
        ++ [ ( max 1 $ 10 - Map.size (regs s),
               Some <$> (Register <$> probablyUnregistered s <*> arbitraryVar ctx)
             )
             | not . null $ ctxAtType @ThreadId ctx
           ]

  shrinkAction ctx _ (Register name tid) =
    [Some (Unregister name)]
      ++ [Some (Register name' tid) | name' <- shrinkName name]
      ++ [Some (Register name tid') | tid' <- shrinkVar ctx tid]
  shrinkAction _ _ (Unregister name) =
    Some (WhereIs name) : [Some (Unregister name') | name' <- shrinkName name]
  shrinkAction _ _ (WhereIs name) =
    [Some (WhereIs name') | name' <- shrinkName name]
  shrinkAction _ _ Spawn = []
  shrinkAction ctx _ (KillThread tid) =
    [Some (KillThread tid') | tid' <- shrinkVar ctx tid]

  initialState = RegState mempty []

  nextState s Spawn _ = s
  nextState s (Register name tid) _step = s {regs = Map.insert name tid (regs s)}
  nextState s (Unregister name) _step =
    s {regs = Map.delete name (regs s)}
  nextState s (KillThread tid) _ =
    s
      { dead = tid : dead s,
        regs = Map.filter (/= tid) (regs s)
      }
  nextState s WhereIs {} _ = s

type RegM = ReaderT Registry IO

instance RunModel RegState RegM where
  perform _ Spawn _ = do
    lift $ forkIO (threadDelay 10000000)
  perform _ (Register name tid) env = do
    reg <- ask
    lift $ try $ register reg name (env tid)
  perform _ (Unregister name) _ = do
    reg <- ask
    lift $ try $ unregister reg name
  perform _ (WhereIs name) _ = do
    reg <- ask
    lift $ whereis reg name
  perform _ (KillThread tid) env = do
    lift $ killThread (env tid)
    lift $ threadDelay 100

  postcondition (s, _) (WhereIs name) env mtid = do
    pure $ (env <$> Map.lookup name (regs s)) == mtid
  postcondition _ Register {} _ res = do
    pure $ isRight res
  postcondition _ _ _ _ = pure True

  postconditionOnFailure (s, _) act@Register {} _ res = do
    monitorPost $
      tabulate
        "Reason for -Register"
        [ why s act
          | Left {} <- [res]
        ]
    pure $ isLeft res
  postconditionOnFailure _s _ _ _ = pure True

  monitoring (_s, s') act@(showDictAction -> ShowDict) _ res =
    counterexample (show res ++ " <- " ++ show act ++ "\n  -- State: " ++ show s')
      . tabulate "Registry size" [show $ Map.size (regs s')]

data ShowDict a where
  ShowDict :: (Show (Realized RegM a)) => ShowDict a

showDictAction :: forall a. Action RegState a -> ShowDict a
showDictAction Spawn {} = ShowDict
showDictAction WhereIs {} = ShowDict
showDictAction Register {} = ShowDict
showDictAction Unregister {} = ShowDict
showDictAction KillThread {} = ShowDict

why :: RegState -> Action RegState a -> String
why s (Register name tid) =
  unwords $
    ["name already registered" | name `Map.member` regs s]
      ++ ["tid already registered" | tid `elem` Map.elems (regs s)]
      ++ ["dead thread" | tid `elem` dead s]
why _ _ = "(impossible)"

arbitraryName :: Gen String
arbitraryName = elements allNames

probablyRegistered :: RegState -> Gen String
probablyRegistered s = oneof $ map pure (Map.keys $ regs s) ++ [arbitraryName]

probablyUnregistered :: RegState -> Gen String
probablyUnregistered s = elements $ allNames ++ (allNames \\ Map.keys (regs s))

shrinkName :: String -> [String]
shrinkName name = [n | n <- allNames, n < name]

allNames :: [String]
allNames = ["a", "b", "c", "d", "e"]

runPropertyReaderT :: (Monad m) => PropertyM (ReaderT e m) a -> e -> PropertyM m a
runPropertyReaderT p e = MkPropertyM $ \k -> do
  m <- unPropertyM p $ fmap lift . k
  return $ runReaderT m e

prop_Registry :: Actions RegState -> Property
prop_Registry s@(Actions ss) =
  monadicIO $ do
    monitor $ counterexample "\nExecution\n"
    reg <- lift setupRegistry
    runPropertyReaderT (runActions s) reg
    QC.assert True