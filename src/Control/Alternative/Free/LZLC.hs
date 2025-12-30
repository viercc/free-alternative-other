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
  Free(.., SumOf, AzOf),

  Summand(..), viewSummand,
  Factor(..), viewFactor,

  viewSum, reviewSum,
  viewAz, reviewAz,

  -- * Universal properties
  hoistFree, liftFree, foldFree,

  -- * Auxiliary definitions
  Trivial(..),
  Sum,
  NontrivialSum(..),
  NontrivialAz(..)
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
-- way is to use 'AzOf' and 'SumOf' pattern synonyms, along with
-- 'viewFactor' and 'viewSummand' to pattern match on @Factor@ and @Summand@
-- further.
data Free f a where
  FreeTrivial :: Trivial f a -> Free f a
  FreeSumOf' :: NontrivialSum (Summand f) a -> Free f a
  FreeAzOf' :: NontrivialAz (Factor f) a -> Free f a
  deriving Functor

instance (Functor f) => Applicative (Free f) where
  pure = FreeTrivial . TrivialPure
  x <*> y = reviewAz (viewAz x <*> viewAz y)

instance (Functor f) => Alternative (Free f) where
  empty = FreeTrivial TrivialZero
  x <|> y = reviewSum (viewSum x <> viewSum y)

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
    runSummand :: Either (f a) (NontrivialAz (Factor f) a) }
  deriving (Functor) via Lift1 (FCompose NontrivialAz Factor) f
  deriving (FFunctor) via Lift1 (FCompose NontrivialAz Factor)

-- | Subexpressions of @'Free' f a@ which can't be written as any one of
--
-- * @empty@
-- * @pure a@
-- * Nontrivial product @x <*> y@
newtype Factor f a = Factor {
    runFactor :: Either (f a) (NontrivialSum (Summand f) a) }
  deriving (Functor) via Lift1 (FCompose NontrivialSum Summand) f
  deriving (FFunctor) via Lift1 (FCompose NontrivialSum Summand)

viewSum :: Free f a -> Sum (Summand f) a
viewSum e = case e of
  FreeTrivial tfa -> trivialSum $ hoistTrivial (Summand . Left) tfa
  FreeSumOf' fas -> toSum fas
  FreeAzOf' fas -> pure . Summand . Right $ fas

reviewSum :: Sum (Summand f) a -> Free f a
reviewSum e = case nontrivialSum e of
  Left tfa  -> trivialFree injectSummand tfa
  Right fas    -> FreeSumOf' fas
  where
    injectSummand :: Summand f a -> Free f a
    injectSummand = either liftFree FreeAzOf' . runSummand

-- | View @Free f a@ as a sum of @Summand f@, terminated by
--   either @Nil@ or @Zee a@ (corresponding @empty@ or @pure a@ respectively)
pattern SumOf :: Sum (Summand f) a -> Free f a
pattern SumOf sz <- (viewSum -> sz)
  where SumOf sz = reviewSum sz

{-# COMPLETE SumOf #-}

viewAz :: Free f a -> Az (Factor f) a
viewAz e = case e of
  FreeTrivial tfa -> trivialAz $ hoistTrivial (Factor . Left) tfa
  FreeSumOf' fas -> liftAz . Factor . Right $ fas
  FreeAzOf' fas -> toAz fas

reviewAz :: Functor f => Az (Factor f) a -> Free f a
reviewAz e = case nontrivialAz e of
  Left tfa -> trivialFree injectFactor tfa
  Right fas    -> FreeAzOf' fas
  where
    injectFactor :: Factor f a -> Free f a
    injectFactor = either liftFree FreeSumOf' . runFactor

-- | View @Free f a@ as a product of @Factor f@, terminated by
--   either @'Zero'@ or @'Pure' a@ (corresponding @empty@ or @pure a@ respectively)
pattern AzOf :: Functor f => () => Az (Factor f) a -> Free f a
pattern AzOf az <- (viewAz -> az)
  where AzOf az = reviewAz az

{-# COMPLETE AzOf #-}

-- | @Summand f a@ is either @f a@ or a product of multiple @Factor f@ values.
--   The @Right@ case never returns a trivial summand, which is one of
--
-- * @'Zero'@,
-- * @'Pure' a@,
-- * @'liftAz' fac@ for one @fac :: Factor f a@
viewSummand :: Summand f a -> Either (f a) (Az (Factor f) a)
viewSummand = fmap toAz . runSummand

-- | @Factor f a@ is either @f a@ or a sum of multiple @Summand f@ values.
--   The @Right@ case never returns a trivial factor, which is one of
--
-- * @'Nil'@,
-- * @'Zee' a@,
-- * @'Cons' suma Nil@ for one @suma :: Summand f a@
viewFactor :: Factor f a -> Either (f a) (Sum (Summand f) a)
viewFactor = fmap toSum . runFactor

hoistFree :: (forall x. f x -> g x) -> Free f a -> Free g a
hoistFree fg e = case e of
  FreeTrivial tfa -> FreeTrivial (hoistTrivial fg tfa)
  FreeSumOf' fas -> FreeSumOf' (hoistNontrivialSum (hoistSummand fg) fas)
  FreeAzOf' fas -> FreeAzOf' (hoistNontrivialAz (hoistFactor fg) fas)

hoistFactor :: (forall x. f x -> g x) -> Factor f a -> Factor g a
hoistFactor fg = Factor . bimap fg (hoistNontrivialSum (hoistSummand fg)) . runFactor

hoistSummand :: (forall x. f x -> g x) -> Summand f a -> Summand g a
hoistSummand fg = Summand . bimap fg (hoistNontrivialAz (hoistFactor fg)) . runSummand

liftFree :: f a -> Free f a
liftFree = FreeTrivial . TrivialLift

foldFree :: forall f g a. (Alternative g) => (forall x. f x -> g x) -> Free f a -> g a
foldFree handle = goSum . viewSum
  where
    goSum :: forall b. Sum (Summand f) b -> g b
    goSum = foldrZ empty pure ((<|>) . goSummand)

    goSummand :: forall b. Summand f b -> g b
    goSummand = either handle goAz . viewSummand

    goAz :: forall b. Az (Factor f) b -> g b
    goAz = foldAz goFactor empty

    goFactor :: forall b. Factor f b -> g b
    goFactor = either handle goSum . viewFactor

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
type Sum f a = ListZ a (f a)

-- | @Trivial f a + NontrivialSum f a ~ Sum f a = ListZ a (f a)@
data NontrivialSum f a =
    ConsZee (f a) a
  | ConsMany (f a) (f a) (ListZ a (f a))

instance Functor f => Functor (NontrivialSum f) where
  fmap h e = case e of
    ConsZee fa a -> ConsZee (fmap h fa) (h a)
    ConsMany fa fa' rest -> ConsMany (fmap h fa) (fmap h fa') (bimap h (fmap h) rest)

instance FFunctor NontrivialSum where
  ffmap = hoistNontrivialSum

hoistNontrivialSum :: (forall x. f x -> g x) -> NontrivialSum f a -> NontrivialSum g a
hoistNontrivialSum fg e = case e of
    ConsZee fa a -> ConsZee (fg fa) a
    ConsMany fa fa' rest -> ConsMany (fg fa) (fg fa') (fmap fg rest)

trivialSum :: Trivial f a -> Sum f a
trivialSum e = case e of
  TrivialZero -> Nil
  TrivialPure a -> Zee a
  TrivialLift fa -> Cons fa Nil

toSum :: NontrivialSum f a -> Sum f a
toSum (ConsZee fa a) = Cons fa (Zee a)
toSum (ConsMany fa fa' rest) = Cons fa (Cons fa' rest)

nontrivialSum :: Sum f a -> Either (Trivial f a) (NontrivialSum f a)
nontrivialSum e = case e of
  Nil -> Left TrivialZero
  Zee a -> Left $ TrivialPure a
  Cons fa Nil -> Left $ TrivialLift fa
  Cons fa (Zee a) -> Right $ ConsZee fa a
  Cons fa (Cons fa' rest) -> Right $ ConsMany fa fa' rest

-- | @Trivial f a + NontrivialAz f a ~ Az f a@
data NontrivialAz f a where
  ApZero :: f a -> NontrivialAz f b
  ApMany :: f a -> f b -> Az f (b -> a -> c) -> NontrivialAz f c

deriving instance Functor (NontrivialAz f)

instance FFunctor NontrivialAz where
  ffmap = hoistNontrivialAz

hoistNontrivialAz :: (forall x. f x -> g x) -> NontrivialAz f a -> NontrivialAz g a
hoistNontrivialAz fg e = case e of
  ApZero fa -> ApZero (fg fa)
  ApMany fa fb rest -> ApMany (fg fa) (fg fb) (hoistAz fg rest)

trivialAz :: Trivial f a -> Az f a
trivialAz e = case e of
  TrivialZero -> Zero
  TrivialPure a -> Pure a
  TrivialLift fa -> liftAz fa

toAz :: NontrivialAz f a -> Az f a
toAz (ApZero fa) = Ap fa Zero
toAz (ApMany fa fb rest) = Ap fa (Ap fb rest)

nontrivialAz :: Functor f => Az f a -> Either (Trivial f a) (NontrivialAz f a)
nontrivialAz e = case e of
  Pure a -> Left $ TrivialPure a
  Zero -> Left TrivialZero
  Ap fa (Pure k) -> Left $ TrivialLift (k <$> fa)
  Ap fa Zero -> Right $ ApZero fa
  Ap fa (Ap fb rest) -> Right $ ApMany fa fb rest
