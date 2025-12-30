{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneKindSignatures #-}
module FFunctor.Tannen where
import FFunctor

-- | Wraps a @FFunctor ff@ inside a @Functor h@.
-- 
-- This can be thought of as a functor composition below.
--
-- > (Functor × Type) -[ff]-> Type -[h]-> Type
-- 
-- The name @Tannen@ is an homage to @Data.Bifunctor.Tannen@
-- in @bifunctors@ package, which works in a similar way: taking @Bifunctor p@ and
--  @Functor h@, makes @Bifunctor@ by the composition below.
-- 
-- > (Type × Type) -[p]-> Type -[f]-> Type
type Tannen :: FUNCTOR -> FF -> FF
newtype Tannen h ff g x = Tannen { runTannen :: h (ff g x) }
  deriving Functor

instance (Functor h, FFunctor ff) => FFunctor (Tannen h ff) where
  ffmap t = Tannen . fmap (ffmap t) . runTannen