{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

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
) where

import Control.Applicative (Alternative (..))
import Control.Applicative.Free.Zero
import Control.Applicative.Free.Zero.Impure

import Data.List.Zero
import Data.List.Zero.NonEmpty
import Data.Bifunctor (Bifunctor(bimap))

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
  FreeAltZero :: Free f a
  FreeAltPure :: a -> Free f a
  FreeAltLift :: f a -> Free f a
  FreeAltSumOf' :: Summand f a -> ListZ' a (Summand f a) -> Free f a
  FreeAltAzOf' :: Factor f a -> Az' (Factor f) (a -> b) -> Free f b

instance Functor f => Functor (Free f) where
  fmap h e = case e of
    FreeAltZero -> FreeAltZero
    FreeAltPure a -> FreeAltPure (h a)
    FreeAltLift fa -> FreeAltLift (fmap h fa)
    FreeAltSumOf' fa rest -> FreeAltSumOf' (fmap h fa) (bimap h (fmap h) rest)
    FreeAltAzOf' fa rest -> FreeAltAzOf' fa (fmap (h .) rest)

-- | Subexpressions of @'Free' f a@ which can't be written as any one of
--
-- * @empty@
-- * @pure a@
-- * Nontrivial sum @x <|> y@
data Summand f a where
  SummandLift :: f a -> Summand f a
  SummandAp :: Factor f a -> Az' (Factor f) (a -> b) -> Summand f b

deriving instance Functor f => Functor (Summand f)

-- | Subexpressions of @'Free' f a@ which can't be written as any one of
--
-- * @empty@
-- * @pure a@
-- * Nontrivial product @x <*> y@
data Factor f a =
    FactorLift (f a)
  | FactorSum (Summand f a) (ListZ' a (Summand f a))

instance Functor f => Functor (Factor f) where
  fmap h (FactorLift fa) = FactorLift (fmap h fa)
  fmap h (FactorSum fa rest) = FactorSum (fmap h fa) (bimap h (fmap h) rest)

viewSum :: Free f a -> ListZ a (Summand f a)
viewSum e = case e of
 FreeAltZero -> Nil
 FreeAltPure a -> Zee a
 FreeAltLift fa -> pure (SummandLift fa)
 FreeAltSumOf' fa fas -> Cons fa (toListZ fas)
 FreeAltAzOf' fa rest -> pure (SummandAp fa rest)

reviewSum :: ListZ a (Summand f a) -> Free f a
reviewSum e = case e of
  Nil -> FreeAltZero
  Zee a -> FreeAltPure a
  Cons z Nil -> injectSummand z
  Cons z (Zee a) -> FreeAltSumOf' z (Zee' a)
  Cons z1 (Cons z2 r) -> FreeAltSumOf' z1 (Cons' z2 r)
  where
    injectSummand :: Summand f a -> Free f a
    injectSummand (SummandLift fa) = FreeAltLift fa
    injectSummand (SummandAp fa rest) = FreeAltAzOf' fa rest

-- | View @Free f a@ as a sum of @Summand f@, terminated by
--   either @Nil@ or @Zee a@ (corresponding @empty@ or @pure a@ respectively)
pattern SumOf :: ListZ a (Summand f a) -> Free f a
pattern SumOf sz <- (viewSum -> sz)

{-# COMPLETE SumOf #-}

viewAz :: Free f a -> Az (Factor f) a
viewAz e = case e of
 FreeAltZero -> Zero
 FreeAltPure a -> Pure a
 FreeAltLift fa -> liftAz (FactorLift fa)
 FreeAltSumOf' fa fas -> liftAz (FactorSum fa fas)
 FreeAltAzOf' fa rest -> Ap fa (toAz rest)

reviewAz :: Functor f => Az (Factor f) a -> Free f a
reviewAz e = case e of
  Zero -> FreeAltZero
  Pure a -> FreeAltPure a
  Ap z (Pure k) -> injectFactor (k <$> z)
  Ap z Zero -> FreeAltAzOf' z Zero'
  Ap z1 (Ap z2 r) -> FreeAltAzOf' z1 (Ap' z2 r)
  where
    injectFactor :: Factor f a -> Free f a
    injectFactor (FactorLift fa) = FreeAltLift fa
    injectFactor (FactorSum fa fas) = FreeAltSumOf' fa fas

-- | View @Free f a@ as a product of @Factor f@, terminated by
--   either @'Zero'@ or @'Pure' a@ (corresponding @empty@ or @pure a@ respectively)
pattern AzOf :: Functor f => Az (Factor f) a -> Free f a
pattern AzOf az <- (viewAz -> az)

{-# COMPLETE AzOf #-}

-- | @Summand f a@ is either @f a@ or a product of multiple @Factor f@ values.
--   The @Right@ case never returns a trivial summand, which is one of
--
-- * @'Zero'@,
-- * @'Pure' a@,
-- * @'liftAz' fac@ for one @fac :: Factor f a@
viewSummand :: Summand f a -> Either (f a) (Az (Factor f) a)
viewSummand (SummandLift fa) = Left fa
viewSummand (SummandAp fa rest) = Right (Ap fa (toAz rest))

-- | @Factor f a@ is either @f a@ or a sum of multiple @Summand f@ values.
--   The @Right@ case never returns a trivial factor, which is one of
--
-- * @'Nil'@,
-- * @'Zee' a@,
-- * @'Cons' suma Nil@ for one @suma :: Summand f a@
viewFactor :: Factor f a -> Either (f a) (ListZ a (Summand f a))
viewFactor (FactorLift fa) = Left fa
viewFactor (FactorSum fa rest) = Right $ Cons fa (toListZ rest)

instance (Functor f) => Applicative (Free f) where
  pure = FreeAltPure
  x <*> y = reviewAz (viewAz x <*> viewAz y)

instance (Functor f) => Alternative (Free f) where
  empty = FreeAltZero
  x <|> y = reviewSum (viewSum x <> viewSum y)

hoistFree :: forall f g a. (forall x. f x -> g x) -> Free f a -> Free g a
hoistFree fg e = case e of
  FreeAltZero -> FreeAltZero
  FreeAltPure a -> FreeAltPure a
  FreeAltLift fa -> FreeAltLift (fg fa)
  FreeAltSumOf' fa fas -> FreeAltSumOf' (goSummand fa) (fmap goSummand fas)
  FreeAltAzOf' fa rest -> FreeAltAzOf' (goFactor fa) (hoistAz' goFactor rest)
  where 
    goFactor :: forall b. Factor f b -> Factor g b
    goFactor (FactorLift fb) = FactorLift $ fg fb
    goFactor (FactorSum fb fbs) = FactorSum (goSummand fb) (fmap goSummand fbs)

    goSummand :: forall b. Summand f b -> Summand g b
    goSummand (SummandLift fb) = SummandLift $ fg fb
    goSummand (SummandAp fb rest)  = SummandAp (goFactor fb) (hoistAz' goFactor rest)

liftFree :: f a -> Free f a
liftFree = FreeAltLift

foldFree :: forall f g a. (Alternative g) => (forall x. f x -> g x) -> Free f a -> g a
foldFree handle = goSum . viewSum
  where
    goSum :: forall b. ListZ b (Summand f b) -> g b
    goSum = foldrZ empty pure (\fa r -> goSummand fa <|> r)

    goAp :: forall b. Az (Factor f) b -> g b
    goAp = foldAz goFactor empty

    goFactor :: forall b. Factor f b -> g b
    goFactor (FactorLift fb) = handle fb
    goFactor (FactorSum fb fbs) = goSum (Cons fb (toListZ fbs))

    goSummand :: forall b. Summand f b -> g b
    goSummand (SummandLift fb) = handle fb
    goSummand (SummandAp fb fbs)  = goAp (Ap fb (toAz fbs))
