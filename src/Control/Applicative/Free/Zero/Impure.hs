{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE RankNTypes #-}

module Control.Applicative.Free.Zero.Impure(
  Az'(..),
  hoistAz', toAz
) where

import Control.Applicative.Free.Zero

-- | 'Az' sans 'Pure'.
data Az' f a where
  Zero' :: Az' f a
  Ap' :: f a -> Az f (a -> b) -> Az' f b

instance Functor (Az' f) where
  fmap _ Zero' = Zero'
  fmap f (Ap' fa rest) = Ap' fa (fmap (f .) rest)

hoistAz' :: (forall x. f x -> g x) -> Az' f a -> Az' g a
hoistAz' _  Zero' = Zero'
hoistAz' fg (Ap' fa rest) = Ap' (fg fa) (hoistAz fg rest)

toAz :: Az' f a -> Az f a
toAz Zero' = Zero
toAz (Ap' fa rest) = Ap fa rest
