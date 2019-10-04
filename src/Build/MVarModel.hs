{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Build.MVarModel where

import Prelude hiding (lookup)

import GHC.Base (Any)
import Unsafe.Coerce (unsafeCoerce)
import Control.Monad.IO.Class (MonadIO)
import Control.Applicative (liftA2)
import Data.Proxy
import Control.Monad.Reader (ReaderT(..), MonadReader(..), liftIO, asks)
import Algebra.Graph (Graph)
import Data.List (sort)
import qualified Algebra.Graph as G
import Data.IntMap (IntMap)
import qualified Data.IntMap as M
import Data.Dynamic (Dynamic, Typeable)
import qualified Data.Dynamic as D
import Data.Maybe (fromJust)
import Data.Tagged (Tagged(..))
import Control.Concurrent.MVar (modifyMVar, modifyMVar_, takeMVar, putMVar, newMVar, readMVar, newEmptyMVar, tryReadMVar, MVar)
import Control.Exception.Base (evaluate)
import Data.Functor ((<&>), ($>))
import Control.Concurrent (forkIO, threadDelay)
import qualified Data.IntSet as S
import Data.IntSet (IntSet)

type family Append xs ys where
  Append '[] ys = ys
  Append (x ': xs) ys = x ': Append xs ys

data DepL (xs :: [*]) where
  DEmpty :: DepL '[]
  DCons  :: Tagged a Int -> DepL as -> DepL (a ': as)

(<+>) :: DepL xs -> DepL ys -> DepL (Append xs ys)
(<+>) DEmpty ys = ys
(<+>) (DCons x xs) ys = DCons x (xs <+> ys)

infixr 6 <+>

toIntList :: DepL xs -> [Int]
toIntList DEmpty = []
toIntList (DCons (Tagged i) xs) = i : toIntList xs

toIntSet :: DepL xs -> IntSet
toIntSet = S.fromList . toIntList

type Produce c = DepL '[c]

type Depend xs = DepL xs

type family Args xs a where
  Args '[] a = a
  Args (x ': xs) a = x -> Args xs a

data HList (xs :: [*]) where
  HNil  :: HList '[]
  HCons :: a -> HList as -> HList (a ': as)

uncurryN :: Args xs a -> HList xs -> a
uncurryN f HNil = f
uncurryN f (HCons a as) = uncurryN (f a) as

class Monad m => MonadBuild m where
  depend   :: Args xs (m a) -> Depend xs -> m (Produce a)
  tryBuild :: Produce a -> m (Maybe a)

produce :: MonadBuild m => m a -> m (Produce a)
produce x = depend x DEmpty

-- Block everything until the Produce a is built
build :: MonadBuild m => Produce a -> m a
build p = go
  where
    go = tryBuild p >>= maybe go pure

foo :: (MonadIO m, MonadBuild m) => m ()
foo = do
  a1 <- produce $ liftIO (threadDelay 1000000) $> 10
  a2 <- produce $ liftIO (threadDelay 2000000) $> 10
  a3 <- depend (\x y -> liftIO (threadDelay 1000000) $> x + y) (a1 <+> a2)
  a4 <- depend (\x -> liftIO (putStrLn "a4") *> pure (x + 1)) a1
  r  <- build a3
  r' <- build a4
  liftIO $ print (r, r')

nested :: (MonadIO m, MonadBuild m) => m ()
nested = do
  a1 <- produce $ liftIO (threadDelay 1000000) $> 10
  a2 <- depend nest1 a1
  r1 <- build a2
  r2 <- build r1
  liftIO $ print r2
  where
    nest1 x = do
      a1 <- produce $ liftIO (threadDelay 1000000) $> 10
      depend (\y -> pure $ x + y) a1

data Env = Env
  { envProds :: MVar (IntMap (MVar Any))
  , envGetId :: IO Int
  }

newEnv :: IO Env
newEnv = do
  ps <- newMVar M.empty
  iv <- newMVar 0
  let gid = modifyMVar iv (\i -> pure (i + 1, i))
  pure $ Env ps gid

newtype Build a = Build (ReaderT Env IO a)
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader Env
           , MonadIO
           )

runBuild :: Build a -> Env -> IO a
runBuild (Build m) e = runReaderT m e

nextId :: Build Int
nextId = asks envGetId >>= liftIO

readProds :: Build (IntMap (MVar Any))
readProds = asks envProds >>= liftIO . readMVar

newStep :: Build (Int, MVar Any)
newStep = do
  ps <- asks envProds
  i  <- nextId
  liftIO $ do
    mv <- newEmptyMVar
    modifyMVar_ ps (pure . M.insert i mv)
    pure (i, mv)

instance MonadBuild Build where
  depend = dependImpl
  tryBuild = tryBuildImpl

dependImpl :: forall xs a. Args xs (Build a) -> Depend xs -> Build (Produce a)
dependImpl a ds = do
  env <- ask
  (i, rmv) <- newStep
  liftIO $ forkIO $ do
    ds' <- runBuild (fetchDeps ds) env
    r   <- runBuild (uncurryN @xs @(Build a) a ds') env
    putMVar rmv (unsafeCoerce r)
  pure $ DCons (Tagged i) DEmpty
  where
    fetchDeps :: DepL as -> Build (HList as)
    fetchDeps ds = do
      submap <- readProds >>= liftIO . filteredRead
      pure $ castDeps ds submap
        where
          filteredRead m = traverse readMVar $ M.restrictKeys m (toIntSet ds)

    castDeps :: DepL as -> IntMap Any -> HList as
    castDeps DEmpty _ = HNil
    castDeps (DCons (Tagged i) xs) m = HCons getOne (castDeps xs m)
      where
        getOne = unsafeCoerce (fromJust $ M.lookup i m)

tryBuildImpl :: Produce a -> Build (Maybe a)
tryBuildImpl (DCons (Tagged i) DEmpty) = do
  m <- asks envProds
  r <- liftIO $ readMVar m >>= maybe (pure Nothing) tryReadMVar . M.lookup i
  pure $ unsafeCoerce <$> r

