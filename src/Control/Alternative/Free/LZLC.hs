{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingVia #-}

-- | Free alternative (with /left zero/ + /left catch/).
--
-- 'Alternative' laws were not set to one, clear definition,
-- but there are two major ones.
--
-- For an instance of @(Alternative f)@, both laws have these in common.
--
-- - Inherited laws from 'Applicative'
-- - @(f a, 'empty', '<|>')@ forms monoid for any type @a@.
-- - /Left zero/ law: @'empty' '<*>' x === 'empty'@.
--
-- Candidate #1 of the Alternative law have /Left distribution/ law.
--
-- @
-- -- Left distribution
-- (x '<|>' y) '<*>' z === (x \<*\> z) \<|\> (y \<*\> z)
-- @
--
-- Another candidate #2 have /Left catch/ law instead.
--
-- @
-- -- Left catch
-- 'pure' x '<|>' y === pure x
-- @
--
-- Reference Typeclassopedia <https://wiki.haskell.org/Typeclassopedia#Laws_6>
-- for more about these laws.
--
-- The \"free alternative\" construction for the alternative #1
-- (with /Left distribution/) is known and implemented.
--
-- - https://people.cs.kuleuven.be/~tom.schrijvers/Research/talks/ppdp2015.pdf
-- - <https://hackage.haskell.org/package/free-5.2/docs/Control-Alternative-Free.html>
--
-- This module provides the free alternative #2.
module Control.Alternative.Free.LZLC(
  -- * Type definitions
  Free(.., SumZOf, ApZOf),

  Summand(..), viewSummand,
  Factor(..), viewFactor,

  viewSumZ, reviewSumZ,
  viewApZ, reviewApZ,

  -- * Universal properties
  hoistFree, liftFree, foldFree,

  -- * Auxiliary definitions
  Trivial(..),
  SumZ,
  NontrivialSumZ(..),
  NontrivialApZ(..)
) where

import Control.Applicative (Alternative (..))
import Control.Applicative.Free.Zero

import Data.List.Zero
import Data.Bifunctor (Bifunctor(bimap))
import FFunctor
import FFunctor.Lift1
import FFunctor.FCompose
import FMonad

-- * Type definitions

-- | The Free (left zero + left catch) 'Alternative'.
-- 
-- The constructors of @Free@ is named intentionally verbose.
-- 
-- To construct a value of @Free f a@, a convenient and recommended
-- way is to use 'liftFree' and methods of @Alternative (Free f)@ instances.
--
-- To pattern match a value of @Free f a@, a convenient and recommended
-- way is to use 'ApZOf' and 'SumZOf' pattern synonyms, along with
-- 'viewFactor' and 'viewSummand' to pattern match on @Factor@ and @Summand@
-- further.
data Free f a where
  FreeTrivial :: Trivial f a -> Free f a
  FreeSumZOf' :: NontrivialSumZ (Summand f) a -> Free f a
  FreeApZOf' :: NontrivialApZ (Factor f) a -> Free f a
  deriving Functor

instance (Functor f) => Applicative (Free f) where
  pure = FreeTrivial . TrivialPure
  x <*> y = reviewApZ (viewApZ x <*> viewApZ y)

instance (Functor f) => Alternative (Free f) where
  empty = FreeTrivial TrivialZero
  x <|> y = reviewSumZ (viewSumZ x <> viewSumZ y)

instance FFunctor Free where
  ffmap = hoistFree

instance FMonad Free where
  fpure = liftFree
  fbind = foldFree

-- | Subexpressions of @'Free' f a@ which can't be written as any one of
--
-- * @empty@
-- * @pure a@
-- * Nontrivial sum @x <|> y@
newtype Summand f a = Summand {
    runSummand :: Either (f a) (NontrivialApZ (Factor f) a) }
  deriving (Functor) via Lift1 (FCompose NontrivialApZ Factor) f
  deriving (FFunctor) via Lift1 (FCompose NontrivialApZ Factor)

-- | Subexpressions of @'Free' f a@ which can't be written as any one of
--
-- * @empty@
-- * @pure a@
-- * Nontrivial product @x <*> y@
newtype Factor f a = Factor {
    runFactor :: Either (f a) (NontrivialSumZ (Summand f) a) }
  deriving (Functor) via Lift1 (FCompose NontrivialSumZ Summand) f
  deriving (FFunctor) via Lift1 (FCompose NontrivialSumZ Summand)

viewSumZ :: Free f a -> SumZ (Summand f) a
viewSumZ e = case e of
  FreeTrivial tfa -> trivialSumZ $ hoistTrivial (Summand . Left) tfa
  FreeSumZOf' fas -> toSumZ fas
  FreeApZOf' fas -> pure . Summand . Right $ fas

reviewSumZ :: SumZ (Summand f) a -> Free f a
reviewSumZ e = case nontrivialSumZ e of
  Left tfa  -> trivialFree injectSummand tfa
  Right fas    -> FreeSumZOf' fas
  where
    injectSummand :: Summand f a -> Free f a
    injectSummand = either liftFree FreeApZOf' . runSummand

-- | View @Free f a@ as a sum of @Summand f@, terminated by
--   either @Nil@ or @Zee a@ (corresponding @empty@ or @pure a@ respectively)
pattern SumZOf :: SumZ (Summand f) a -> Free f a
pattern SumZOf sz <- (viewSumZ -> sz)
  where SumZOf sz = reviewSumZ sz

{-# COMPLETE SumZOf #-}

viewApZ :: Free f a -> ApZ (Factor f) a
viewApZ e = case e of
  FreeTrivial tfa -> trivialApZ $ hoistTrivial (Factor . Left) tfa
  FreeSumZOf' fas -> liftApZ . Factor . Right $ fas
  FreeApZOf' fas -> toApZ fas

reviewApZ :: Functor f => ApZ (Factor f) a -> Free f a
reviewApZ e = case nontrivialApZ e of
  Left tfa -> trivialFree injectFactor tfa
  Right fas    -> FreeApZOf' fas
  where
    injectFactor :: Factor f a -> Free f a
    injectFactor = either liftFree FreeSumZOf' . runFactor

-- | View @Free f a@ as a product of @Factor f@, terminated by
--   either @'Zero'@ or @'Pure' a@ (corresponding @empty@ or @pure a@ respectively)
pattern ApZOf :: Functor f => () => ApZ (Factor f) a -> Free f a
pattern ApZOf az <- (viewApZ -> az)
  where ApZOf az = reviewApZ az

{-# COMPLETE ApZOf #-}

-- | @Summand f a@ is either @f a@ or a product of multiple @Factor f@ values.
--   The @Right@ case never returns a trivial summand, which is one of
--
-- * @'Zero'@,
-- * @'Pure' a@,
-- * @'liftApZ' fac@ for one @fac :: Factor f a@
viewSummand :: Summand f a -> Either (f a) (ApZ (Factor f) a)
viewSummand = fmap toApZ . runSummand

-- | @Factor f a@ is either @f a@ or a sum of multiple @Summand f@ values.
--   The @Right@ case never returns a trivial factor, which is one of
--
-- * @'Nil'@,
-- * @'Zee' a@,
-- * @'Cons' suma Nil@ for one @suma :: Summand f a@
viewFactor :: Factor f a -> Either (f a) (SumZ (Summand f) a)
viewFactor = fmap toSumZ . runFactor

hoistFree :: (forall x. f x -> g x) -> Free f a -> Free g a
hoistFree fg e = case e of
  FreeTrivial tfa -> FreeTrivial (hoistTrivial fg tfa)
  FreeSumZOf' fas -> FreeSumZOf' (hoistNontrivialSumZ (hoistSummand fg) fas)
  FreeApZOf' fas -> FreeApZOf' (hoistNontrivialApZ (hoistFactor fg) fas)

hoistFactor :: (forall x. f x -> g x) -> Factor f a -> Factor g a
hoistFactor fg = Factor . bimap fg (hoistNontrivialSumZ (hoistSummand fg)) . runFactor

hoistSummand :: (forall x. f x -> g x) -> Summand f a -> Summand g a
hoistSummand fg = Summand . bimap fg (hoistNontrivialApZ (hoistFactor fg)) . runSummand

liftFree :: f a -> Free f a
liftFree = FreeTrivial . TrivialLift

foldFree :: forall f g a. (Alternative g) => (forall x. f x -> g x) -> Free f a -> g a
foldFree handle = goSumZ . viewSumZ
  where
    goSumZ :: forall b. SumZ (Summand f) b -> g b
    goSumZ = foldrZ empty pure ((<|>) . goSummand)

    goSummand :: forall b. Summand f b -> g b
    goSummand = either handle goApZ . viewSummand

    goApZ :: forall b. ApZ (Factor f) b -> g b
    goApZ = foldApZ goFactor empty

    goFactor :: forall b. Factor f b -> g b
    goFactor = either handle goSumZ . viewFactor

----

-- | Trivial expressions
data Trivial f a = TrivialZero | TrivialPure a | TrivialLift (f a)
  deriving (Functor)

hoistTrivial :: (forall x. f x -> g x) -> Trivial f a -> Trivial g a
hoistTrivial fg e = case e of
  TrivialZero -> TrivialZero
  TrivialPure a -> TrivialPure a
  TrivialLift fa -> TrivialLift (fg fa)

trivialFree :: (forall x. f x -> Free g x) -> Trivial f a -> Free g a
trivialFree k e = case e of
  TrivialZero -> FreeTrivial TrivialZero
  TrivialPure a -> FreeTrivial (TrivialPure a)
  TrivialLift fa -> k fa

-- | Formal sum of @f a@ ending in either @pure a@ (@Zee a@) or @empty@ (Nil).
type SumZ f a = ListZ a (f a)

-- | @Trivial f a + NontrivialSumZ f a ~ SumZ f a = ListZ a (f a)@
data NontrivialSumZ f a =
    ConsZee (f a) a
  | ConsMany (f a) (f a) (ListZ a (f a))

instance Functor f => Functor (NontrivialSumZ f) where
  fmap h e = case e of
    ConsZee fa a -> ConsZee (fmap h fa) (h a)
    ConsMany fa fa' rest -> ConsMany (fmap h fa) (fmap h fa') (bimap h (fmap h) rest)

instance FFunctor NontrivialSumZ where
  ffmap = hoistNontrivialSumZ

hoistNontrivialSumZ :: (forall x. f x -> g x) -> NontrivialSumZ f a -> NontrivialSumZ g a
hoistNontrivialSumZ fg e = case e of
    ConsZee fa a -> ConsZee (fg fa) a
    ConsMany fa fa' rest -> ConsMany (fg fa) (fg fa') (fmap fg rest)

trivialSumZ :: Trivial f a -> SumZ f a
trivialSumZ e = case e of
  TrivialZero -> Nil
  TrivialPure a -> Zee a
  TrivialLift fa -> Cons fa Nil

toSumZ :: NontrivialSumZ f a -> SumZ f a
toSumZ (ConsZee fa a) = Cons fa (Zee a)
toSumZ (ConsMany fa fa' rest) = Cons fa (Cons fa' rest)

nontrivialSumZ :: SumZ f a -> Either (Trivial f a) (NontrivialSumZ f a)
nontrivialSumZ e = case e of
  Nil -> Left TrivialZero
  Zee a -> Left $ TrivialPure a
  Cons fa Nil -> Left $ TrivialLift fa
  Cons fa (Zee a) -> Right $ ConsZee fa a
  Cons fa (Cons fa' rest) -> Right $ ConsMany fa fa' rest

-- | @Trivial f a + NontrivialApZ f a ~ ApZ f a@
data NontrivialApZ f a where
  ApZero :: f a -> NontrivialApZ f b
  ApMany :: f a -> f b -> ApZ f (b -> a -> c) -> NontrivialApZ f c

deriving instance Functor (NontrivialApZ f)

instance FFunctor NontrivialApZ where
  ffmap = hoistNontrivialApZ

hoistNontrivialApZ :: (forall x. f x -> g x) -> NontrivialApZ f a -> NontrivialApZ g a
hoistNontrivialApZ fg e = case e of
  ApZero fa -> ApZero (fg fa)
  ApMany fa fb rest -> ApMany (fg fa) (fg fb) (hoistApZ fg rest)

trivialApZ :: Trivial f a -> ApZ f a
trivialApZ e = case e of
  TrivialZero -> Zero
  TrivialPure a -> Pure a
  TrivialLift fa -> liftApZ fa

toApZ :: NontrivialApZ f a -> ApZ f a
toApZ (ApZero fa) = Ap fa Zero
toApZ (ApMany fa fb rest) = Ap fa (Ap fb rest)

nontrivialApZ :: Functor f => ApZ f a -> Either (Trivial f a) (NontrivialApZ f a)
nontrivialApZ e = case e of
  Pure a -> Left $ TrivialPure a
  Zero -> Left TrivialZero
  Ap fa (Pure k) -> Left $ TrivialLift (k <$> fa)
  Ap fa Zero -> Right $ ApZero fa
  Ap fa (Ap fb rest) -> Right $ ApMany fa fb rest
