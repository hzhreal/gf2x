module Algebra where

class Ring a where
  zero :: a
  zero' :: a -> a
  one :: a
  one' :: a -> a

  iden :: a -> a

  addInv :: a -> a

  (.+.) :: a -> a -> a
  (.*.) :: a -> a -> a

  (.-.) :: a -> a -> a
  (.**.) :: (Integral b) => a -> b -> a

  (.==.) :: a -> a -> Bool
  (.!=.) :: a -> a -> Bool

class (Ring a) => EuclidanDomain a where
  (.%.) :: a -> a -> a
  (./.) :: a -> a -> a

class (Ring a) => Field a where
  mulInv :: a -> a

  (.***.) :: (Integral b) => a -> b -> a
