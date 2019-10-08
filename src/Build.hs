{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE ConstraintKinds            #-}

module Build where

import GHC.Base (Any)
import Algebra.Graph (Graph)
import qualified Algebra.Graph as G
import qualified Algebra.Graph.ToGraph as TG
import Control.Applicative (liftA2)
import Control.Monad.Trans.Free (FreeT(..), MonadFree(..), liftF, iterTM)
import Control.Monad.State (StateT, gets, modify, runStateT)
import Control.Monad (join)
import Data.Functor.Identity (Identity)
import Data.Functor (($>), (<$), (<&>), void)
import Data.IntMap (IntMap)
import qualified Data.IntSet as S
import Data.Maybe (fromJust)
import Data.Foldable (traverse_)
import Data.Function ((&))
import qualified Data.IntMap as M
import Unsafe.Coerce (unsafeCoerce)
import Control.Concurrent (MVar, newEmptyMVar, readMVar, putMVar, takeMVar, forkIO)
import Data.SOP (NP(..), I(..), K(..), All(..), Top(..))
import qualified Data.SOP as SOP
import qualified Data.SOP.NP as SOP
import Data.SOP.Dict (pureAll, Dict(..))
import Lens.Micro.TH (makeLenses)
import Lens.Micro ((%~))
import Lens.Micro.Mtl ((%=), (+=), use)

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

type Tag as = NP (K Int) as

(<+>) :: NP f xs -> NP f ys -> NP f (Append xs ys)
(<+>) Nil ys = ys
(<+>) (x :* xs) ys = x :* (xs <+> ys)

infixr 6 <+>

toIntList :: Tag xs -> [Int]
toIntList d = SOP.collapse_NP d

-- A Kleisli arrow along with data about how to locate its input
data DKleisli as m b where
  DKleisli :: Dict (All Top) as -> Tag as -> (NP I as -> m b) -> DKleisli as m b

instance Functor m => Functor (DKleisli as m) where
  fmap f (DKleisli d t g) = DKleisli d t (fmap f . g)

get :: (Applicative m) => Tag '[x] -> DKleisli '[x] m x
get t = DKleisli pureAll t (\(I x :* _) -> pure x)

(<**>) :: (All Top (Append xs ys), Applicative m)
       => DKleisli xs m (a -> b)
       -> DKleisli ys m a
       -> DKleisli (Append xs ys) m b
(<**>) (DKleisli _ t1 f) (DKleisli _ t2 g) = DKleisli pureAll (t1 <+> t2) go
  where
    go x = let (xs, ys) = partitionAt t1 x
           in f xs <*> g ys

    partitionAt :: Tag xs -> NP I (Append xs ys) -> (NP I xs, NP I ys)
    partitionAt Nil ys = (Nil, ys)
    partitionAt (_ :* xs) (x :* xs') = let (nxs, nys) = partitionAt xs xs'
                                   in (x :* nxs, nys)

infixl 4 <**>

joinDK :: Monad m => DKleisli as m (m b) -> DKleisli as m b
joinDK (DKleisli d t f) = DKleisli d t (join . f)

getDKTag :: DKleisli as m b -> Tag as
getDKTag (DKleisli _ t _) = t

data BuildF m x where
  Step :: Maybe String -> DKleisli as m b -> (Tag '[b] -> x) -> BuildF m x

deriving instance Functor (BuildF m)

type BuildT m n a = FreeT (BuildF m) n a

type MBF m n = MonadFree (BuildF m) n

step' :: (MBF m n, All Top as) => Maybe String -> DKleisli as m b -> n (Tag '[b])
step' l k = liftF $ Step l k id

step :: (MBF m n, All Top as) => DKleisli as m b -> n (Tag '[b])
step = step' Nothing

-- Add a step that feeds the product of n inputs to a function of arity n
dependN' :: (MBF m n, All Top as) => Maybe String -> Args as (m b) -> Tag as -> n (Tag '[b])
dependN' l a d = step' l (DKleisli pureAll d (uncurryN a))

dependN :: (MBF m n, All Top as) => Args as (m b) -> Tag as -> n (Tag '[b])
dependN = dependN' Nothing

-- Add a step with no inputs
produce' :: MBF m n => Maybe String -> m a -> n (Tag '[a])
produce' l a = dependN' l a Nil

produce :: MBF m n => m a -> n (Tag '[a])
produce = produce' Nothing

data WithId a b = WithId { getId :: a, getVal :: b }

instance (Show a, Show b) => Show (WithId a b) where
  show (WithId a b) = "WithId " <> show a <> " " <> show b

instance Eq a => Eq (WithId a b) where
  (==) (WithId a _) (WithId a' _) = a == a'

instance Ord a => Ord (WithId a b) where
  compare (WithId a _) (WithId a' _) = compare a a'

data ExistsDK m where
  MkEx :: Maybe String -> DKleisli as m b -> ExistsDK m

instance Show (ExistsDK m) where
  show (MkEx ml _) = "ExistsDK" <> maybe "" (\l -> " " <> l) ml

type DepGraph m = Graph (WithId Int (ExistsDK m))

data SEnv m = SEnv
  { _nextId    :: Int
  , _existsMap :: IntMap (ExistsDK m)
  , _depGraph  :: Graph Int
  }

makeLenses ''SEnv

emptyEnv :: SEnv m
emptyEnv = SEnv 0 M.empty G.empty

-- intermediate interpretation monad
type SI m n a = StateT (SEnv m) n a

interpretS :: forall m n a. Monad n => BuildT m n a -> SI m n a
interpretS = iterTM go
  where
    go (Step ml dk next) = do
      i <- use nextId <* (nextId += 1)
      insertDep i (toIntList $ getDKTag dk) (MkEx ml dk)
      next $ K i :* Nil

    insertDep i ds k = do
      existsMap %= M.insert i k
      depGraph  %= G.overlay (G.star i ds)

-- Construct the entire graph
buildDepGraph :: IntMap (ExistsDK m) -> Graph Int -> Maybe (DepGraph m)
buildDepGraph m = G.foldg e v o c
  where
    e = Just G.empty
    v i = G.vertex . WithId i <$> M.lookup i m
    o mx my = liftA2 G.overlay mx my
    c mx my = liftA2 G.connect mx my

-- Construct a graph of the dependencies of a specific id (partial, id must be in the map)
buildGraphOf :: forall m. Int -> IntMap (ExistsDK m) -> DepGraph m
buildGraphOf i m = case M.lookup i m of
  Just x@(MkEx _ (DKleisli _ (ds :: Tag xs) (act :: NP I xs -> m b))) ->
    let is  = toIntList ds
        ds' = fromJust $ traverse (\a -> WithId a <$> M.lookup a m) is
        sg  = G.star (WithId i x) ds'
    in G.overlays $ sg : fmap (flip buildGraphOf m) is
  Nothing -> G.empty


-- Turns out having the full graph isn't actually very useful, except for debugging/testing
fullGraphS :: Monad n => SI m n a -> n ((a, Maybe (DepGraph m)))
fullGraphS m = runStateT m emptyEnv <&> \(a, e) -> (a, buildDepGraph (_existsMap e) (_depGraph e))

fullGraph :: Monad n => BuildT m n a -> n ((a, Maybe (DepGraph m)))
fullGraph = fullGraphS . interpretS

-- Interpret BuildT and compute the DAG of `Tag '[a]`'s dependencies
graphOf :: Monad n => BuildT m n (Tag '[a]) -> n (Tag '[a], DepGraph m)
graphOf b = runStateT (interpretS b) emptyEnv <&> go
  where
    go :: (Tag '[a], SEnv m) -> (Tag '[a], DepGraph m)
    go (p@(K i :* Nil), env) = (p, buildGraphOf i (_existsMap env))

build :: forall m a. Monad m => Tag '[a] -> DepGraph m -> m (Maybe a)
build (K i :* _) g = case TG.topSort g of
 Nothing -> pure Nothing
 Just ts -> let c = foldr exec (pure M.empty) ts
             in fmap (fmap unsafeFromAny . M.lookup i) c
  where
    exec :: WithId Int (ExistsDK m) -> m (IntMap Any) -> m (IntMap Any)
    exec (WithId i (MkEx _ (DKleisli ad ds act))) mc = do
      cache <- mc
      let ds' = fetchDeps ad ds cache
      r <- act ds'
      pure $ M.insert i (unsafeToAny r) cache

-- A concurrent version of `build` specialized to IO
buildIO :: Tag '[a] -> DepGraph IO -> IO (Maybe a)
buildIO (K i :* _) g = case TG.topSort g of
  Nothing -> pure Nothing
  Just ts -> do
    cache <- initCache $ getId <$> ts
    traverse_ (mkBuilder cache) ts
    r <- traverse readMVar (M.lookup i cache)
    pure $ fmap unsafeFromAny r
  where
    initCache :: [Int] -> IO (IntMap (MVar Any))
    initCache = foldMap (\i -> M.singleton i <$> newEmptyMVar)

    mkBuilder :: IntMap (MVar Any) -> WithId Int (ExistsDK IO) -> IO ()
    mkBuilder m (WithId i (MkEx _ (DKleisli ad ds act))) = void $ forkIO $ do
      sm <- filteredRead
      let ds' = fetchDeps ad ds sm
          mv  = fromJust $ M.lookup i m
      r <- act ds'
      putMVar mv $ unsafeToAny r
      where
        filteredRead = traverse readMVar $ M.restrictKeys m $ S.fromList $ toIntList ds

fetchDeps :: Dict (All Top) xs -> Tag xs -> IntMap Any -> NP I xs
fetchDeps ad ds m = case ad of
  Dict -> SOP.hliftA go ds
  where
    go :: forall x. K Int x -> I x
    go (K i) = pure $ unsafeFromAny $ fromJust $ M.lookup i m

runBuildT :: (Monad m, Monad n) => BuildT m n (Tag '[a]) -> n (m (Maybe a))
runBuildT b = graphOf b <&> uncurry build

runBuildTIO :: Monad n => BuildT IO n (Tag '[a]) -> n (IO (Maybe a))
runBuildTIO b = graphOf b <&> uncurry buildIO

unsafeFromAny :: Any -> a
unsafeFromAny = unsafeCoerce

unsafeToAny :: a -> Any
unsafeToAny = unsafeCoerce

foo :: BuildT IO Identity (Tag '[Int])
foo = do
  a0 <- produce $ putStrLn "Do IO stuff here" *> pure 10
  a1 <- produce $ pure 20
  a2 <- dependN (\x y -> pure (x + y)) (a0 <+> a1)
  a3 <- produce $ putStrLn "look it's stuff" *> pure 10

  -- unused stuff won't be in `graphOf foo`
  u1 <- produce $ putStrLn "No thanks"
  u2 <- produce $ pure "Not today"

  -- depend can take any arity:
  a4 <- dependN (\x y z -> pure (x + y + z)) (a0 <+> a3 <+> a2)

  -- applicative syntax:
  a5 <- step $ (\a b c -> a * b * c) <$> get a1 <**> get a2 <**> get a3

  -- labelled vertices:
  step' (Just "Final Product") $ joinDK $ (\x -> putStrLn "Done!" $> x * 2) <$> get a5

bar :: BuildT IO Identity (Tag '[String])
bar = do
  a1 <- produce $ pure 10
  a2 <- produce $ pure "lol"
  a3 <- dependN (\x y -> pure $ x + length y) (a1 <+> a2)
  dependN (pure . show) a3
