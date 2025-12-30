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
-- This module provides the free @Applicative@ with zero, 'Az',
-- like the free applicative 'Control.Applicative.Az.Ap'.
module Control.Applicative.Free.Zero(
  Az(..),
  liftAz, hoistAz, trap,
  
  foldAz, foldMaybeT, retract
) where

import Control.Applicative (Alternative(..), (<**>))
import FFunctor
import FMonad

-- | Free (applicative with left zero).
data Az f a where
  Pure :: a -> Az f a
  Zero :: Az f a
  Ap :: f a -> Az f (a -> b) -> Az f b

instance Functor (Az f) where
  fmap f (Pure r) = Pure (f r)
  fmap _ Zero = Zero
  fmap f (Ap fa mk) = Ap fa ((f .) <$> mk)

instance Applicative (Az f) where
  pure = Pure

  liftA2 op (Pure x) y = op x <$> y
  liftA2 _ Zero _ = Zero
  liftA2 op (Ap fa mk) y = Ap fa (liftA2 (\g b a -> op (g a) b) mk y)

-- | /Left zero/ + /Left catch/
instance Alternative (Az f) where
  empty = Zero
  (<|>) = trap

liftAz :: f a -> Az f a
liftAz fa = Ap fa (Pure id)

hoistAz :: (forall x. f x -> g x) -> Az f a -> Az g a
hoistAz _ (Pure a) = Pure a
hoistAz _ Zero = Zero
hoistAz fg (Ap fa mk) = Ap (fg fa) (hoistAz fg mk)

instance FFunctor Az where
  ffmap = hoistAz

instance FMonad Az where
  fpure = liftAz
  fbind k = foldAz k Zero

-- | Recovery from 'Zero'.
--
-- @'trap' x y@ first look at @x@ if it ends with @Zero@ constructor.
-- If @x@ ends with @Pure@, return @x@ itself.
-- Otherwise, it replaces @Zero@ in x with @y@.
--
-- @
-- 'trap' (Ap f1 (Ap f2 ... Zero)) y === Ap f1 (Ap f2 ... y)
-- @
trap :: Az f a -> Az f a -> Az f a
trap = go id
  where
    go :: (b -> a) -> Az f a -> Az f b -> Az f a
    go _ (Pure a) _ = Pure a
    go p Zero y = p <$> y
    go p (Ap fa mk) y = Ap fa (go (const . p) mk y)

-- * Interpreting

foldAz :: Applicative g => (forall r. f r -> g r) -> (forall r. g r) -> Az f a -> g a
foldAz handle z e = case e of
  Pure a -> pure a
  Zero -> z
  Ap fa mk -> handle fa <**> foldAz handle z mk

foldMaybeT :: Monad g => (forall r. f r -> g r) -> Az f a -> g (Maybe a)
foldMaybeT _ (Pure a) = pure (Just a)
foldMaybeT _ Zero = pure Nothing
foldMaybeT h (Ap fa mk) = h fa >>= \a -> fmap ($ a) <$> foldMaybeT h mk 

retract :: Alternative f => Az f a -> f a
retract = foldAz id empty
