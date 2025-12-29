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
  -- * Free alternative type 
  Free(.., SumOf, AzOf),

  Summand(..), viewSummand,
  Factor(..), viewFactor,

  viewSum, reviewSum,
  viewAz, reviewAz,

  -- * Utility functions
  hoistFree, liftFree, foldFree,

  -- * Auxiliary types
  Az(..),
  Az'(..), hoistAz', toAz,
  Sz(..), mapSz, foldSz, singletonSz,
  Sz'(..), mapSz', toSz
) where

import Control.Applicative (Alternative (..))
import Control.Applicative.Free.Zero (Az)
import qualified Control.Applicative.Free.Zero as Az

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
  FreeAltSumOf' :: Summand f a -> Sz' (Summand f) a -> Free f a
  FreeAltAzOf' :: Factor f a -> Az' (Factor f) (a -> b) -> Free f b

deriving instance Functor f => Functor (Free f)

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
  | FactorSum (Summand f a) (Sz' (Summand f) a)
  deriving (Functor)

viewSum :: Free f a -> Sz (Summand f) a
viewSum e = case e of
 FreeAltZero -> Nil
 FreeAltPure a -> Zee a
 FreeAltLift fa -> singletonSz (SummandLift fa)
 FreeAltSumOf' fa fas -> Cons fa (toSz fas)
 FreeAltAzOf' fa rest -> singletonSz (SummandAp fa rest)

reviewSum :: Sz (Summand f) a -> Free f a
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
pattern SumOf :: Sz (Summand f) a -> Free f a
pattern SumOf sz <- (viewSum -> sz)

{-# COMPLETE SumOf #-}

viewAz :: Free f a -> Az (Factor f) a
viewAz e = case e of
 FreeAltZero -> Az.Zero
 FreeAltPure a -> Az.Pure a
 FreeAltLift fa -> Az.liftAz (FactorLift fa)
 FreeAltSumOf' fa fas -> Az.liftAz (FactorSum fa fas)
 FreeAltAzOf' fa rest -> Az.Ap fa (toAz rest)

reviewAz :: Functor f => Az (Factor f) a -> Free f a
reviewAz e = case e of
  Az.Zero -> FreeAltZero
  Az.Pure a -> FreeAltPure a
  Az.Ap z (Az.Pure k) -> injectFactor (k <$> z)
  Az.Ap z Az.Zero -> FreeAltAzOf' z Zero'
  Az.Ap z1 (Az.Ap z2 r) -> FreeAltAzOf' z1 (Ap' z2 r)
  where
    injectFactor :: Factor f a -> Free f a
    injectFactor (FactorLift fa) = FreeAltLift fa
    injectFactor (FactorSum fa fas) = FreeAltSumOf' fa fas

-- | View @Free f a@ as a product of @Factor f@, terminated by
--   either @'Az.Zero'@ or @'Az.Pure' a@ (corresponding @empty@ or @pure a@ respectively)
pattern AzOf :: Functor f => Az (Factor f) a -> Free f a
pattern AzOf az <- (viewAz -> az)

{-# COMPLETE AzOf #-}

-- | @Summand f a@ is either @f a@ or a product of multiple @Factor f@ values.
--   The @Right@ case never returns a trivial summand, which is one of
--
-- * @'Az.Zero'@,
-- * @'Az.Pure' a@,
-- * @'Az.liftAz' fac@ for one @fac :: Factor f a@
viewSummand :: Summand f a -> Either (f a) (Az (Factor f) a)
viewSummand (SummandLift fa) = Left fa
viewSummand (SummandAp fa rest) = Right (Az.Ap fa (toAz rest))

-- | @Factor f a@ is either @f a@ or a sum of multiple @Summand f@ values.
--   The @Right@ case never returns a trivial factor, which is one of
--
-- * @'Nil'@,
-- * @'Zee' a@,
-- * @'Cons' suma Nil@ for one @suma :: Summand f a@
viewFactor :: Factor f a -> Either (f a) (Sz (Summand f) a)
viewFactor (FactorLift fa) = Left fa
viewFactor (FactorSum fa rest) = Right $ Cons fa (toSz rest)

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
  FreeAltSumOf' fa fas -> FreeAltSumOf' (goSummand fa) (mapSz' goSummand fas)
  FreeAltAzOf' fa rest -> FreeAltAzOf' (goFactor fa) (hoistAz' goFactor rest)
  where 
    goFactor :: forall b. Factor f b -> Factor g b
    goFactor (FactorLift fb) = FactorLift $ fg fb
    goFactor (FactorSum fb fbs) = FactorSum (goSummand fb) (mapSz' goSummand fbs)

    goSummand :: forall b. Summand f b -> Summand g b
    goSummand (SummandLift fb) = SummandLift $ fg fb
    goSummand (SummandAp fb rest)  = SummandAp (goFactor fb) (hoistAz' goFactor rest)

liftFree :: f a -> Free f a
liftFree = FreeAltLift

foldFree :: forall f g a. (Alternative g) => (forall x. f x -> g x) -> Free f a -> g a
foldFree handle = goSum . viewSum
  where
    goSum :: forall b. Sz (Summand f) b -> g b
    goSum = foldSz empty pure (\fa r -> goSummand fa <|> r)

    goAp :: forall b. Az (Factor f) b -> g b
    goAp = Az.foldAz goFactor empty

    goFactor :: forall b. Factor f b -> g b
    goFactor (FactorLift fb) = handle fb
    goFactor (FactorSum fb fbs) = goSum (Cons fb (toSz fbs))

    goSummand :: forall b. Summand f b -> g b
    goSummand (SummandLift fb) = handle fb
    goSummand (SummandAp fb fbs)  = goAp (Az.Ap fb (toAz fbs))

-- * Auxiliary types

-- | Non-@Pure@ products.
data Az' f a where
  Zero' :: Az' f a
  Ap' :: f a -> Az f (a -> b) -> Az' f b

instance Functor (Az' f) where
  fmap _ Zero' = Zero'
  fmap f (Ap' fa rest) = Ap' fa (fmap (f .) rest)

hoistAz' :: (forall x. f x -> g x) -> Az' f a -> Az' g a
hoistAz' _  Zero' = Zero'
hoistAz' fg (Ap' fa rest) = Ap' (fg fa) (Az.hoistAz fg rest)

toAz :: Az' f a -> Az f a
toAz Zero' = Az.Zero
toAz (Ap' fa rest) = Az.Ap fa rest

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

-- | Non-@Nil@ sum.
data Sz' f a = Zee' a | Cons' (f a) (Sz f a)
  deriving (Functor)

mapSz' :: (f a -> g a) -> Sz' f a -> Sz' g a
mapSz' _  (Zee' a) = Zee' a
mapSz' fg (Cons' fa rest) = Cons' (fg fa) (mapSz fg rest) 

toSz :: Sz' f a -> Sz f a
toSz (Zee' a) = Zee a
toSz (Cons' fa1 rest) = Cons fa1 rest