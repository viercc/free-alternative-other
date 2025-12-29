{-# LANGUAGE DeriveTraversable #-}
module Data.List.NotOne(
  NotOne(..), notOne, toList
) where

import Data.Foldable (Foldable(..))

data NotOne a = Nil | TwoOrMore a a [a]
  deriving (Show, Read, Eq, Ord, Functor, Traversable)

notOne :: [a] -> Either a (NotOne a)
notOne [] = Right Nil
notOne [a] = Left a
notOne (a0:a1:as) = Right (TwoOrMore a0 a1 as)

instance Foldable NotOne where
  foldr f z = foldr f z . toList

  toList Nil = []
  toList (TwoOrMore a0 a1 as) = a0 : a1 : as

  null Nil = True
  null _ = False

instance Semigroup (NotOne a) where
  Nil <> y = y
  TwoOrMore a0 a1 as <> y = TwoOrMore a0 a1 (as ++ toList y)

instance Monoid (NotOne a) where
  mempty = Nil
