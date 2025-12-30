{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE RankNTypes #-}

-- | An applicative with left zero @f@ is an 'Applicative'
-- with polymorphic zero action which stops
-- all actions right to zero.
--
-- @
-- -- Type of zero action
-- zero :: forall a. f a
-- 
-- -- Left zero law
-- zero \<*\> x === zero
-- @
-- 
-- This module provides the free @Applicative@ with zero, 'ApZ',
-- like the free applicative 'Control.Applicative.ApZ.Ap'.
module Control.Applicative.Free.Zero(
  ApZ(..),
  liftApZ, hoistApZ, trap,
  
  foldApZ, foldMaybeT, retract
) where

import Control.Applicative (Alternative(..), (<**>))
import FFunctor
import FMonad

-- | Free (applicative with left zero).
data ApZ f a where
  Pure :: a -> ApZ f a
  Zero :: ApZ f a
  Ap :: f a -> ApZ f (a -> b) -> ApZ f b

instance Functor (ApZ f) where
  fmap f (Pure r) = Pure (f r)
  fmap _ Zero = Zero
  fmap f (Ap fa mk) = Ap fa ((f .) <$> mk)

instance Applicative (ApZ f) where
  pure = Pure

  liftA2 op (Pure x) y = op x <$> y
  liftA2 _ Zero _ = Zero
  liftA2 op (Ap fa mk) y = Ap fa (liftA2 (\g b a -> op (g a) b) mk y)

-- | /Left zero/ + /Left catch/
instance Alternative (ApZ f) where
  empty = Zero
  (<|>) = trap

liftApZ :: f a -> ApZ f a
liftApZ fa = Ap fa (Pure id)

hoistApZ :: (forall x. f x -> g x) -> ApZ f a -> ApZ g a
hoistApZ _ (Pure a) = Pure a
hoistApZ _ Zero = Zero
hoistApZ fg (Ap fa mk) = Ap (fg fa) (hoistApZ fg mk)

instance FFunctor ApZ where
  ffmap = hoistApZ

instance FMonad ApZ where
  fpure = liftApZ
  fbind k = foldApZ k Zero

-- | Recovery from 'Zero'.
--
-- @'trap' x y@ first look at @x@ if it ends with @Zero@ constructor.
-- If @x@ ends with @Pure@, return @x@ itself.
-- Otherwise, it replaces @Zero@ in x with @y@.
--
-- @
-- 'trap' (Ap f1 (Ap f2 ... Zero)) y === Ap f1 (Ap f2 ... y)
-- @
trap :: ApZ f a -> ApZ f a -> ApZ f a
trap = go id
  where
    go :: (b -> a) -> ApZ f a -> ApZ f b -> ApZ f a
    go _ (Pure a) _ = Pure a
    go p Zero y = p <$> y
    go p (Ap fa mk) y = Ap fa (go (const . p) mk y)

-- * Interpreting

foldApZ :: Applicative g => (forall r. f r -> g r) -> (forall r. g r) -> ApZ f a -> g a
foldApZ handle z e = case e of
  Pure a -> pure a
  Zero -> z
  Ap fa mk -> handle fa <**> foldApZ handle z mk

foldMaybeT :: Monad g => (forall r. f r -> g r) -> ApZ f a -> g (Maybe a)
foldMaybeT _ (Pure a) = pure (Just a)
foldMaybeT _ Zero = pure Nothing
foldMaybeT h (Ap fa mk) = h fa >>= \a -> fmap ($ a) <$> foldMaybeT h mk 

retract :: Alternative f => ApZ f a -> f a
retract = foldApZ id empty
