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
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}

module Build where

import GHC.Base (Any)
import Algebra.Graph (Graph)
import qualified Algebra.Graph as G
import qualified Algebra.Graph.ToGraph as TG
import Control.Applicative (liftA2)
import Control.Monad.Trans.Free (FreeT(..), MonadFree(..), liftF, iterTM)
import Control.Monad.State (StateT, gets, modify, runStateT)
import Data.Functor.Identity (Identity)
import Data.Functor (($>), (<$), (<&>))
import Data.Tagged (Tagged(..))
import Data.IntMap (IntMap)
import Data.Maybe (fromJust)
import qualified Data.IntMap as M
import Unsafe.Coerce

type family Append xs ys where
  Append '[] ys = ys
  Append (x ': xs) ys = x ': Append xs ys

-- Collects function arguments into a type-level list, e.g. (a -> b -> c) = Args '[a, b] c
type family Args (xs :: [*]) (a :: *) where
  Args '[] a = a
  Args (x ': xs) a = x -> Args xs a

data HList (xs :: [*]) where
  HNil  :: HList '[]
  HCons :: a -> HList as -> HList (a ': as)

-- To avoid fiddling with type errors from `HList (Map Annot xs)` all day
data TagList (xs :: [*]) where
  TNil  :: TagList '[]
  TCons :: Tagged a Int -> TagList as -> TagList (a ': as)

(<+>) :: TagList xs -> TagList ys -> TagList (Append xs ys)
(<+>) TNil ys = ys
(<+>) (TCons x xs) ys = TCons x (xs <+> ys)

infixr 6 <+>

type Produce c = TagList '[c]

type Depends xs = TagList xs

toIntList :: TagList xs -> [Int]
toIntList TNil = []
toIntList (TCons (Tagged x) xs) = x : toIntList xs

uncurryN :: Args xs a -> HList xs -> a
uncurryN f HNil = f
uncurryN f (HCons a as) = uncurryN (f a) as

data WithId a b = WithId a b deriving Show

instance Eq a => Eq (WithId a b) where
  (==) (WithId a _) (WithId a' _) = a == a'

instance Ord a => Ord (WithId a b) where
  compare (WithId a _) (WithId a' _) = compare a a'

data ExistsK m where
  ExistsK :: (HList xs -> m b) -> Depends xs -> ExistsK m

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
  Depend :: Args as (m b) -> Depends as -> (Produce b -> x) -> BuildF m x

deriving instance Functor (BuildF m)

depend :: (MonadFree (BuildF m) n) => Args as (m b) -> Depends as -> n (Produce b)
depend a d = liftF (Depend a d id)

produce :: (MonadFree (BuildF m) n) => m b -> n (Produce b)
produce act = depend act TNil

type BuildT m n a = FreeT (BuildF m) n a

data SEnv m = SEnv
  { senvNextId :: Int
  , senvMap    :: IntMap (ExistsK m)
  , senvGraph  :: Graph Int
  }

emptyEnv :: SEnv m
emptyEnv = SEnv 0 M.empty G.empty

interpretS :: forall m n a. Monad n => BuildT m n a -> StateT (SEnv m) n a
interpretS = iterTM go
  where
    --Manually bring everything into scope because the typechecker gets confused with the GADT
    go (Depend
        (act :: Args as (m b))
        (ds :: Depends as)
        (next :: Produce b -> StateT (SEnv m) n a)
       ) = do
      i <- nextId
      case ds of
        TNil -> insertDep i [] (ExistsK (const act) ds)
        _    -> insertDep i (toIntList ds) (ExistsK (uncurryN @as @(m b) act) ds)
      next $ mkProduce i

    nextId = gets senvNextId <* modify (\e -> e { senvNextId = senvNextId e + 1 })

    insertDep i ds k = modify go
      where
        go e = e { senvMap   = M.insert i k (senvMap e)
                 , senvGraph = G.overlay (G.star i ds) (senvGraph e)
                 }

    mkProduce i = TCons (Tagged i) TNil

graphS :: Monad n => StateT (SEnv m) n a -> n ((a, Maybe (DepGraph m)))
graphS m = runStateT m emptyEnv <&> \(a, e) -> (a, buildDepGraph (senvMap e) (senvGraph e))

graph :: Monad n => BuildT m n a -> n ((a, Maybe (DepGraph m)))
graph = graphS . interpretS

build :: forall m a. Monad m => Produce a -> DepGraph m -> m (Maybe a)
build (TCons (Tagged i) TNil) g = case TG.topSort g of
  Just g' -> let c = foldr exec (pure M.empty) g'
             in fmap (fmap unsafeCoerce . M.lookup i) c
  Nothing -> pure Nothing
  where
    exec :: WithId Int (ExistsK m) -> m (IntMap Any) -> m (IntMap Any)
    exec (WithId i (ExistsK act ds)) mc = do
      cache <- mc
      let ds' = fetchDeps ds cache
      r <- act ds'
      pure $ M.insert i (unsafeCoerce r) cache

    fetchDeps :: Depends xs -> IntMap Any -> HList xs
    fetchDeps TNil _ = HNil
    fetchDeps (TCons (Tagged i) xs) m = HCons getOne $ fetchDeps xs m
      where
        getOne = unsafeCoerce $ fromJust (M.lookup i m)

runBuildT :: (Monad m, Monad n) => BuildT m n (Produce a) -> n (m (Maybe a))
runBuildT b = graph b <&> maybe (pure Nothing) (uncurry build) . sequenceA

foo :: BuildT IO Identity (Produce Int)
foo = do
  a1 <- produce $ putStrLn "Do IO stuff here" *> pure 10
  a2 <- produce $ pure 20
  a3 <- depend (\x y -> pure (x + y)) (a1 <+> a2)
  a4 <- produce $ pure 10
  -- depend can take any arity:
  depend (\x y z -> pure (x + y + z)) (a1 <+> a2 <+> a3)

bar :: BuildT IO Identity (Produce String)
bar = do
  a1 <- produce $ pure 10
  a2 <- produce $ pure "lol"
  a3 <- depend (\x y -> pure $ x + length y) (a1 <+> a2)
  depend (pure . show) a3
