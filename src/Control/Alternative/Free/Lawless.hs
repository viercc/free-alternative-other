{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | Free @Alternative@ (with no laws beyond monoidal).
--
-- Free 'Alternative' but assumes no laws relating
-- @Applicative@ structure and @Alternative@ methods,
-- just inherited @Applicative@ laws and @(empty, '<|>')@ being
-- monoid.
module Control.Alternative.Free.Lawless(
  -- * Type definitions
  Free(.., SumOf, ApOf),
  Factor(..), Summand(..),
  viewAp, reviewAp, viewSum, reviewSum,

  -- * Universal property
  liftFree, hoistFree, foldFree,

  -- * Auxiliary types
  Ap'(..), toAp, notOneAp
) where

import Control.Applicative (Alternative (..))
import Control.Applicative.Free

import Data.List.NotOne
import Data.Foldable (asum)

data Free f a =
    FreeLift (f a)
  | FreeSumOf' (NotOne (Summand f a))
  | FreeApOf'  (Ap' (Factor f) a)
  deriving Functor

instance Functor f => Applicative (Free f) where
  pure = reviewAp . pure
  x <*> y = reviewAp (viewAp x <*> viewAp y)

instance Functor f => Alternative (Free f) where
  empty = reviewSum empty
  x <|> y = reviewSum (viewSum x <|> viewSum y)

-- | View as a list of 'Summand's
pattern SumOf :: [Summand f a] -> Free f a
pattern SumOf fas <- (viewSum -> fas)
  where SumOf fas = reviewSum fas

viewSum :: Free f a -> [Summand f a]
viewSum e = case e of
 FreeLift fa -> pure (SummandLift fa)
 FreeSumOf' fas -> toList fas
 FreeApOf' fas -> pure (SummandAp fas)

reviewSum :: [Summand f a] -> Free f a
reviewSum = either injectSummand FreeSumOf' . notOne
  where
    injectSummand :: Summand f a -> Free f a
    injectSummand (SummandLift fa) = FreeLift fa
    injectSummand (SummandAp fas) = FreeApOf' fas

-- | View as a @Ap@, formal chain of @<*>@, of 'Factor's.
pattern ApOf :: Functor f => () => Ap (Factor f) a -> Free f a
pattern ApOf fas <- (viewAp -> fas)
  where ApOf fas = reviewAp fas

viewAp :: Free f a -> Ap (Factor f) a
viewAp e = case e of
  FreeLift fa -> liftAp (FactorLift fa)
  FreeSumOf' fas -> liftAp (FactorSum fas)
  FreeApOf' fas -> toAp fas

reviewAp :: Functor f => Ap (Factor f) a -> Free f a
reviewAp = either injectFactor FreeApOf' . notOneAp
  where
    injectFactor :: Factor f a -> Free f a
    injectFactor (FactorLift fa) = FreeLift fa
    injectFactor (FactorSum fas) = FreeSumOf' fas

-- | Subexpressions of @Free f a@ which cannot be written as
-- nontrivial sum @x '<|>' y@.
data Summand f a =
    SummandLift (f a)
  | SummandAp (Ap' (Factor f) a)
  deriving Functor

-- | Subexpressions of @Free f a@ which cannot be written as
-- nontrivial apply @x '<*>' y@.
data Factor f a =
    FactorLift (f a)
  | FactorSum (NotOne (Summand f a))
  deriving Functor

liftFree :: f a -> Free f a
liftFree = FreeLift

hoistFree :: forall f g a. (forall x. f x -> g x) -> Free f a -> Free g a
hoistFree fg e = case e of
  FreeLift fa -> FreeLift (fg fa)
  FreeSumOf' fas -> FreeSumOf' (fmap goSummand fas)
  FreeApOf' fas -> FreeApOf' (hoistAp' goFactor fas)
  where
    goSummand :: forall b. Summand f b -> Summand g b
    goSummand (SummandLift fb) = SummandLift (fg fb)
    goSummand (SummandAp fas) = SummandAp (hoistAp' goFactor fas)

    goFactor :: forall b. Factor f b -> Factor g b
    goFactor (FactorLift fb) = FactorLift (fg fb)
    goFactor (FactorSum fas) = FactorSum (fmap goSummand fas)

foldFree :: forall f g a. Alternative g => (forall x. f x -> g x) -> Free f a -> g a
foldFree fg e = case e of
  FreeLift fa -> fg fa
  FreeSumOf' fas -> asum (goSummand <$> fas)
  FreeApOf' fas -> runAp goFactor (toAp fas)
  where
    goSummand :: forall b. Summand f b -> g b
    goSummand (SummandLift fa) = fg fa
    goSummand (SummandAp fas) = runAp goFactor (toAp fas)

    goFactor :: forall b. Factor f b -> g b
    goFactor (FactorLift fa) = fg fa
    goFactor (FactorSum fas) = asum (goSummand <$> fas)

-- * Aux

-- | Free Applicative @'Ap' f a@ but @'liftAp' fa@, is excluded.
--
-- @'Ap' f a@ uses zero or more values of @f _@,
-- but @Ap' f a@ uses either none (`Pure'`) or 2+ times (`ApMany'`).
data Ap' f a where
  Pure' :: a -> Ap' f a
  ApMany' :: f a -> f b -> Ap f (b -> a -> c) -> Ap' f c

deriving instance Functor f => Functor (Ap' f) 

hoistAp' :: (forall x. f x -> g x) -> Ap' f a -> Ap' g a
hoistAp' _ (Pure' a) = Pure' a
hoistAp' fg (ApMany' fa fb rest) = ApMany' (fg fa) (fg fb) (hoistAp fg rest)

toAp :: Ap' f a -> Ap f a
toAp (Pure' a) = Pure a
toAp (ApMany' fa fb rest) = Ap fa (Ap fb rest)

notOneAp :: Functor f => Ap f a -> Either (f a) (Ap' f a)
notOneAp (Pure a) = Right (Pure' a)
notOneAp (Ap fa (Pure k)) = Left (k <$> fa)
notOneAp (Ap fa (Ap fb rest)) = Right (ApMany' fa fb rest)

