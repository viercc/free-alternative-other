{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
  Free(..),
  Summand(..),
  Factor(..),

  viewSum, reviewSum, injectSummand,
  viewAp, reviewAp, injectFactor,

  hoistFree, liftFree, foldFree,

  -- * Auxiliary types
  Az, Az'(..), Sz(..), Sz'(..),
) where

import Control.Applicative (Alternative (..))
import Control.Applicative.Free.Zero (Az)
import qualified Control.Applicative.Free.Zero as Az

-- * Type definitions

-- | The Free (left zero + left catch) 'Alternative'.
data Free f a =
    Pure a
  | Zero
  | Lift (f a)
  | SumOf (Sz' (Summand f) a)
  | ApOf (Az' (Factor f) a)
  deriving (Functor)

-- | Subexpressions of @'Free' f a@ which can't be written as any one of
--
-- * @empty@
-- * @pure a@
-- * Nontrivial sum @x <|> y@
data Summand f a =
    SummandLift (f a)
  | SummandAp (Az' (Factor f) a)
  deriving (Functor)

-- | Subexpressions of @'Free' f a@ which can't be written as any one of
--
-- * @empty@
-- * @pure a@
-- * Nontrivial product @x <*> y@
data Factor f a =
    FactorLift (f a)
  | FactorSum (Sz' (Summand f) a)
  deriving (Functor)

injectSummand :: Summand f a -> Free f a
injectSummand (SummandLift fa) = Lift fa
injectSummand (SummandAp fas) = ApOf fas

viewSum :: Free f a -> Sz (Summand f) a
viewSum e = case e of
 (Pure a) -> Zee a
 Zero -> Nil
 (Lift fa) -> singletonSz (SummandLift fa)
 (SumOf fas) -> includeSz' fas
 (ApOf fas) -> singletonSz (SummandAp fas)

reviewSum :: Sz (Summand f) a -> Free f a
reviewSum e = case e of
  Nil -> Zero
  Zee a -> Pure a
  Cons z Nil -> injectSummand z
  Cons z (Zee a) -> SumOf $ SzFz z a
  Cons z1 (Cons z2 r) -> SumOf $ SzLong z1 z2 r

injectFactor :: Factor f a -> Free f a
injectFactor (FactorLift fa) = Lift fa
injectFactor (FactorSum fas) = SumOf fas

viewAp :: Free f a -> Az (Factor f) a
viewAp e = case e of
 (Pure a) -> Az.Pure a
 Zero -> Az.Zero
 (Lift fa) -> singletonAz (FactorLift fa)
 (SumOf fas) -> singletonAz (FactorSum fas)
 (ApOf fas) -> includeAz' fas

reviewAp :: Functor f => Az (Factor f) a -> Free f a
reviewAp e = case e of
  Az.Pure a -> Pure a
  Az.Zero -> Zero
  Az.Ap z (Az.Pure k) -> injectFactor (k <$> z)
  Az.Ap z Az.Zero -> ApOf $ AzFz z
  Az.Ap z1 (Az.Ap z2 r) -> ApOf $ AzLong z1 z2 r

instance (Functor f) => Applicative (Free f) where
  pure = Pure
  x <*> y = reviewAp (viewAp x <*> viewAp y)

instance (Functor f) => Alternative (Free f) where
  empty = Zero
  x <|> y = reviewSum (viewSum x <> viewSum y)

hoistFree :: forall f g a. (forall x. f x -> g x) -> Free f a -> Free g a
hoistFree fg e = case e of
  Pure a -> Pure a
  Zero -> Zero
  Lift fa -> Lift (fg fa)
  SumOf fas -> SumOf (mapSz' goSummand fas)
  ApOf fas -> ApOf (hoistAz' goFactor fas)
  where 
    goFactor :: forall b. Factor f b -> Factor g b
    goFactor (FactorLift fb) = FactorLift $ fg fb
    goFactor (FactorSum fbs) = FactorSum $ mapSz' goSummand fbs

    goSummand :: forall b. Summand f b -> Summand g b
    goSummand (SummandLift fb) = SummandLift $ fg fb
    goSummand (SummandAp fbs)  = SummandAp $ hoistAz' goFactor fbs

liftFree :: f a -> Free f a
liftFree = Lift

foldFree :: forall f g a. (Alternative g) => (forall x. f x -> g x) -> Free f a -> g a
foldFree handle = goSum . viewSum
  where
    goSum :: forall b. Sz (Summand f) b -> g b
    goSum = foldSz empty pure (\fa r -> goSummand fa <|> r)

    goAp :: forall b. Az (Factor f) b -> g b
    goAp = Az.foldAz goFactor empty

    goFactor :: forall b. Factor f b -> g b
    goFactor (FactorLift fb) = handle fb
    goFactor (FactorSum fbs) = goSum (includeSz' fbs)

    goSummand :: forall b. Summand f b -> g b
    goSummand (SummandLift fb) = handle fb
    goSummand (SummandAp fbs)  = goAp (includeAz' fbs)

-- * Auxiliary types

singletonAz :: f a -> Az f a
singletonAz fa = Az.Ap fa (Az.Pure id)

-- | Nontrivial products.
data Az' f a where
  AzFz :: f a -> Az' f b
  AzLong :: f a -> f b -> Az f (b -> a -> c) -> Az' f c

instance Functor (Az' f) where
  fmap _ (AzFz fa) = AzFz fa
  fmap f (AzLong fa fb rest) = AzLong fa fb (fmap (\k b a -> f (k b a)) rest)

hoistAz' :: (forall x. f x -> g x) -> Az' f a -> Az' g a
hoistAz' fg (AzFz fa) = AzFz (fg fa)
hoistAz' fg (AzLong fa fb rest) = AzLong (fg fa) (fg fb) (Az.hoistAz fg rest)

includeAz' :: Az' f a -> Az f a
includeAz' (AzFz fa) = Az.Ap fa Az.Zero
includeAz' (AzLong fa fb rest) = Az.Ap fa (Az.Ap fb rest)

-- | Formal sums of @f a@ with absorbing elements @a@.
data Sz f a =
    Nil    -- ^ Empty sum
  | Zee a  -- ^ Right absorbing elemnet
  | Cons (f a) (Sz f a) -- Append one summand @(f a)@ to the rest 
  deriving (Functor)

singletonSz :: f a -> Sz f a
singletonSz fa = Cons fa Nil

foldSz :: r -> (a -> r) -> (f a -> r -> r) -> Sz f a -> r
foldSz r0 z f =
  let go Nil = r0
      go (Zee a) = z a
      go (Cons fa rest) = f fa (go rest)
  in go

mapSz :: (f a -> g a) -> Sz f a -> Sz g a
mapSz fg = foldSz Nil Zee (Cons . fg)

instance Semigroup (Sz f a) where
  Nil <> y = y
  Zee a <> _ = Zee a
  Cons x xs <> y = Cons x (xs <> y)

instance Monoid (Sz f a) where
  mempty = Nil

-- | Nontrivial sums.
data Sz' f a = SzFz (f a) a | SzLong (f a) (f a) (Sz f a)
  deriving (Functor)

mapSz' :: (f a -> g a) -> Sz' f a -> Sz' g a
mapSz' fg (SzFz fa a) = SzFz (fg fa) a
mapSz' fg (SzLong fa1 fa2 rest) = SzLong (fg fa1) (fg fa2) (mapSz fg rest) 

includeSz' :: Sz' f a -> Sz f a
includeSz' (SzFz fa a) = Cons fa (Zee a)
includeSz' (SzLong fa1 fa2 rest) = Cons fa1 (Cons fa2 rest)