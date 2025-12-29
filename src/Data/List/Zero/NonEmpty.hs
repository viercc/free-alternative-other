{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveTraversable #-}
module Data.List.Zero.NonEmpty where

import AutoLift
import Data.Functor.Classes
import Data.Bifunctor ( Bifunctor(..) )

import Data.List.Zero ( ListZ(Cons, Zee) )

-- | ListZ sans Nil
data ListZ' e a = Zee' e | Cons' a (ListZ e a)
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)
  deriving (Show1, Read1) via (Reflected1 (ListZ' e))
  deriving (Show2, Read2) via (Reflected2 ListZ')

toListZ :: ListZ' e a -> ListZ e a
toListZ (Zee' e) = Zee e
toListZ (Cons' a r) = Cons a r

instance Eq e => Eq1 (ListZ' e)
instance Ord e => Ord1 (ListZ' e)

instance Eq2 ListZ' where
  liftEq2 eqE eqA x y =
    liftEq2 eqE eqA (toListZ x) (toListZ y)

instance Ord2 ListZ' where
  liftCompare2 cmpE cmpA x y =
    liftCompare2 cmpE cmpA (toListZ x) (toListZ y)

instance Bifunctor ListZ' where
  bimap f _ (Zee' e) = Zee' (f e)
  bimap f g (Cons' a r) = Cons' (g a) (bimap f g r)
  
  first f (Zee' e) = Zee' (f e)
  first f (Cons' a r) = Cons' a (first f r)
  
  second = fmap