{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeFamilyDependencies     #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE PolyKinds                  #-}

module Build where

import GHC.Base (Any)
import Algebra.Graph (Graph)
import qualified Algebra.Graph as G
import qualified Algebra.Graph.ToGraph as TG
import Control.Applicative (liftA2)
import Control.Monad.Trans.Free (FreeT(..), MonadFree(..), liftF, iterTM)
import Control.Monad.State (StateT, gets, modify, runStateT)
import Data.Functor.Identity (Identity)
import Data.Functor (($>), (<$), (<&>), void)
import Data.IntMap (IntMap)
import Data.IntSet (IntSet)
import qualified Data.IntSet as S
import Data.Maybe (fromJust)
import Data.Foldable (traverse_)
import qualified Data.IntMap as M
import Unsafe.Coerce (unsafeCoerce)
import Control.Concurrent (MVar, newEmptyMVar, readMVar, putMVar, takeMVar, forkIO)
import Data.SOP (NP(..), I(..), K(..), All(..), Top(..))
import qualified Data.SOP as SOP
import qualified Data.SOP.NP as SOP
import Data.SOP.Dict (pureAll, Dict(..))

type family Append xs ys where
  Append '[] ys = ys
  Append (x ': xs) ys = x ': Append xs ys

-- Collects function arguments into a type-level list, e.g. (a -> b -> c) = Args '[a, b] c
type family Args (xs :: [*]) (a :: *) where
  Args '[] a = a
  Args (x ': xs) a = x -> Args xs a

uncurryN :: Args xs a -> NP I xs -> a
uncurryN a Nil = a
uncurryN f ((I x) :* xs) = uncurryN (f x) xs

type Depends xs = NP (K Int) xs

type Produce a = Depends '[a]

(<+>) :: NP f xs -> NP f ys -> NP f (Append xs ys)
(<+>) Nil ys = ys
(<+>) (x :* xs) ys = x :* (xs <+> ys)

infixr 6 <+>

data WithId a b = WithId { getId :: a, getVal :: b }

instance (Show a, Show b) => Show (WithId a b) where
  show (WithId a b) = "WithId " <> show a <> " " <> show b

instance Eq a => Eq (WithId a b) where
  (==) (WithId a _) (WithId a' _) = a == a'

instance Ord a => Ord (WithId a b) where
  compare (WithId a _) (WithId a' _) = compare a a'

data ExistsK m where
  ExistsK :: Dict (All Top) xs
          -> (NP I xs -> m b)
          -> Depends xs
          -> ExistsK m

instance Show (ExistsK m) where
  show _ = "ExistsK"

type DepGraph m = Graph (WithId Int (ExistsK m))

buildDepGraph :: IntMap (ExistsK m) -> Graph Int -> Maybe (DepGraph m)
buildDepGraph m = G.foldg e v o c
  where
    e = Just G.empty
    v i = G.vertex . WithId i <$> M.lookup i m
    o mx my = liftA2 G.overlay mx my
    c mx my = liftA2 G.connect mx my

data BuildF m x where
  Depend :: Dict (All Top) as
         -> Args as (m b)
         -> Depends as
         -> (Produce b -> x)
         -> BuildF m x

deriving instance Functor (BuildF m)

depend :: (MonadFree (BuildF m) n, All Top as) => Args as (m b) -> Depends as -> n (Produce b)
depend a d = liftF (Depend pureAll a d id)

produce :: (MonadFree (BuildF m) n) => m b -> n (Produce b)
produce act = depend act Nil

type BuildT m n a = FreeT (BuildF m) n a

data SEnv m = SEnv
  { senvNextId :: Int
  , senvMap    :: IntMap (ExistsK m)
  , senvGraph  :: Graph Int
  }

toIntList :: Depends xs -> [Int]
toIntList d = SOP.collapse_NP d

-- Dependencies of a specific id (partial, id MUST be in the map)
buildGraphOf :: forall m. Int -> IntMap (ExistsK m) -> DepGraph m
buildGraphOf i m = case M.lookup i m of
  Just x@(ExistsK _ (act :: NP I xs -> m b) (ds :: Depends xs)) ->
    let is  = toIntList ds
        ds' = fromJust $ traverse (\a -> WithId a <$> M.lookup a m) is
        sg  = G.star (WithId i x) ds'
    in G.overlays $ sg : fmap (flip buildGraphOf m) is
  Nothing -> G.empty

emptyEnv :: SEnv m
emptyEnv = SEnv 0 M.empty G.empty

-- intermediate interpretation monad
type SI m n a = StateT (SEnv m) n a

interpretS :: forall m n a. Monad n => BuildT m n a -> SI m n a
interpretS = iterTM go
  where
    -- Have to manually bring `as` and `b` into scope for `uncurryN` and `next`
    go (Depend ad (act :: Args as (m b)) ds (next :: Produce b -> SI m n a)) = do
      i <- nextId
      case ds of
        Nil -> insertDep i [] (ExistsK ad (const act) ds)
        _   -> insertDep i (toIntList ds) (ExistsK ad (uncurryN @as @(m b) act) ds)
      next $ K i :* Nil

    nextId = gets senvNextId <* modify (\e -> e { senvNextId = senvNextId e + 1 })

    insertDep i ds k = modify go
      where
        go e = e { senvMap   = M.insert i k (senvMap e)
                 , senvGraph = G.overlay (G.star i ds) (senvGraph e)
                 }

-- Turns out having the full graph isn't actually very useful, except for debugging/testing
fullGraphS :: Monad n => StateT (SEnv m) n a -> n ((a, Maybe (DepGraph m)))
fullGraphS m = runStateT m emptyEnv <&> \(a, e) -> (a, buildDepGraph (senvMap e) (senvGraph e))

fullGraph :: Monad n => BuildT m n a -> n ((a, Maybe (DepGraph m)))
fullGraph = fullGraphS . interpretS

-- Interpret BuildT and compute the DAG of `Produce a`'s dependencies
graphOf :: Monad n => BuildT m n (Produce a) -> n (Produce a, DepGraph m)
graphOf b = runStateT (interpretS b) emptyEnv <&> go
  where
    go :: (Produce a, SEnv m) -> (Produce a, DepGraph m)
    go (p@(K i :* Nil), env) = (p, buildGraphOf i (senvMap env))

build :: forall m a. Monad m => Produce a -> DepGraph m -> m (Maybe a)
build (K i :* _) g = case TG.topSort g of
 Nothing -> pure Nothing
 Just ts -> let c = foldr exec (pure M.empty) ts
             in fmap (fmap unsafeFromAny . M.lookup i) c
  where
    exec :: WithId Int (ExistsK m) -> m (IntMap Any) -> m (IntMap Any)
    exec (WithId i (ExistsK ad act ds)) mc = do
      cache <- mc
      let ds' = fetchDeps ad ds cache
      r <- act ds'
      pure $ M.insert i (unsafeToAny r) cache

-- A concurrent version of `build` specialized to IO
buildIO :: Produce a -> DepGraph IO -> IO (Maybe a)
buildIO (K i :* _) g = case TG.topSort g of
  Nothing -> pure Nothing
  Just ts -> do
    cache <- initCache $ getId <$> ts
    traverse_ (mkBuilder cache) ts
    r <- traverse readMVar (M.lookup i cache)
    pure $ fmap unsafeFromAny r
  where
    initCache :: [Int] -> IO (IntMap (MVar Any))
    initCache = fmap M.fromList . traverse (\x -> (x,) <$> newEmptyMVar)

    mkBuilder :: IntMap (MVar Any) -> WithId Int (ExistsK IO) -> IO ()
    mkBuilder m (WithId i (ExistsK ad act ds)) = void $ forkIO $ do
      sm <- filteredRead
      let ds' = fetchDeps ad ds sm
          mv  = fromJust $ M.lookup i m
      r <- act ds'
      putMVar mv $ unsafeToAny r
      where
        filteredRead = traverse readMVar $ M.restrictKeys m (S.fromList $ toIntList ds)

-- Internal function used by build/buildIO
fetchDeps :: Dict (All Top) xs -> Depends xs -> IntMap Any -> NP I xs
fetchDeps ad ds m = case ad of
  Dict -> SOP.hliftA go ds
  where
    go :: forall x. K Int x -> I x
    go (K i) = pure $ unsafeFromAny $ fromJust $ M.lookup i m

runBuildT :: (Monad m, Monad n) => BuildT m n (Produce a) -> n (m (Maybe a))
runBuildT b = graphOf b <&> uncurry build

runBuildTIO :: Monad n => BuildT IO n (Produce a) -> n (IO (Maybe a))
runBuildTIO b = graphOf b <&> uncurry buildIO

unsafeFromAny :: Any -> a
unsafeFromAny = unsafeCoerce

unsafeToAny :: a -> Any
unsafeToAny = unsafeCoerce

foo :: BuildT IO Identity (Produce Int)
foo = do
  a0 <- produce $ putStrLn "Do IO stuff here" *> pure 10
  a1 <- produce $ pure 20
  a2 <- depend (\x y -> pure (x + y)) (a0 <+> a1)
  a3 <- produce $ putStrLn "look it's stuff" *> pure 10

  -- unused stuff won't be in `graphOf foo`
  u1 <- produce $ pure "No thanks"
  u2 <- produce $ pure "Not today"

  -- depend can take any arity:
  depend (\x y z -> pure (x + y + z)) (a0 <+> a3 <+> a2)

bar :: BuildT IO Identity (Produce String)
bar = do
  a1 <- produce $ pure 10
  a2 <- produce $ pure "lol"
  a3 <- depend (\x y -> pure $ x + length y) (a1 <+> a2)
  depend (pure . show) a3
