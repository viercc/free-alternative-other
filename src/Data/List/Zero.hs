{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveTraversable #-}
-- | List with right zero elements (\"Zee\") adjoined.
module Data.List.Zero where

import Control.Monad (ap)

import AutoLift
import Data.Functor.Classes
import Data.Bifunctor ( Bifunctor(..) )

data ListZ e a = Nil | Zee e | Cons a (ListZ e a)
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)
  deriving (Show1, Read1) via (Reflected1 (ListZ e))
  deriving (Show2, Read2) via (Reflected2 ListZ)

instance Eq e => Eq1 (ListZ e)
instance Ord e => Ord1 (ListZ e)

instance Eq2 ListZ where
  liftEq2 eqE eqA = loop
    where
      loop Nil Nil = True
      loop (Zee e1) (Zee e2) = eqE e1 e2
      loop (Cons a1 r1) (Cons a2 r2) = eqA a1 a2 && loop r1 r2
      loop _ _ = False

instance Ord2 ListZ where
  liftCompare2 cmpE cmpA = loop
    where
      loop as1 as2 = case as1 of
        Nil -> case as2 of
          Nil -> EQ
          Zee _ -> LT
          Cons _ _ -> LT
        Zee e1 -> case as2 of
          Nil -> GT
          Zee e2 -> cmpE e1 e2
          Cons _ _ -> LT
        Cons a1 r1 -> case as2 of
          Nil -> GT
          Zee _ -> GT
          Cons a2 r2 -> cmpA a1 a2 <> loop r1 r2

instance Bifunctor ListZ where
  bimap f g = loop
    where
      loop Nil = Nil
      loop (Zee e) = Zee (f e)
      loop (Cons a r) = Cons (g a) (loop r)
  
  first f = loop
    where
      loop Nil = Nil
      loop (Zee e) = Zee (f e)
      loop (Cons a r) = Cons a (loop r)
  
  second = fmap

instance Semigroup (ListZ e a) where
  Nil <> y = y
  Zee e <> _ = Zee e
  Cons a r <> y = Cons a (r <> y)

instance Monoid (ListZ e a) where
  mempty = Nil

instance Applicative (ListZ e) where
  pure a = Cons a Nil
  (<*>) = ap

instance Monad (ListZ e) where
  Nil >>= _ = Nil
  Zee e >>= _ = Zee e
  Cons a r >>= k = k a <> (r >>= k)

foldrZ :: r -> (e -> r) -> (a -> r -> r) -> ListZ e a -> r
foldrZ r0 z f =
  let go Nil = r0
      go (Zee a) = z a
      go (Cons fa rest) = f fa (go rest)
  in go

trap :: ListZ e a -> (e -> ListZ e' a) -> ListZ e' a
trap Nil _ = Nil
trap (Zee e) k = k e
trap (Cons a r) k = Cons a (trap r k)