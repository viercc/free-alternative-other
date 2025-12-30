{-# LANGUAGE RankNTypes #-}
module FFunctor.Lift1 where

import FFunctor
import Data.Bifunctor (Bifunctor(..))

newtype Lift1 ff g x = Lift1 { runLift1 :: Either (g x) (ff g x) }

instance (Functor g, Functor (ff g)) => Functor (Lift1 ff g) where
  fmap t = Lift1 . bimap (fmap t) (fmap t) . runLift1

instance FFunctor ff => FFunctor (Lift1 ff) where
  ffmap gh = Lift1 . bimap gh (ffmap gh) . runLift1