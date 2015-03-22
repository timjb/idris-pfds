module Data.LazyList

%default total
%access public

data LazyListCell a = Nil | (::) a (Lazy (LazyListCell a))

LazyList : Type -> Type
LazyList a = Lazy (LazyListCell a)

(++) : LazyList a -> LazyList a -> LazyList a
(++) xs ys =
  Delay $ case xs of
    Nil => ys
    x::xs' => x::(xs' ++ ys)

instance Semigroup (LazyList a) where
  (<+>) = (++)

instance Monoid (LazyList a) where
  neutral = Nil

instance Functor LazyListCell where
  map f Nil = Nil
  map f (x :: xs) =
    f x :: Delay (let Delay xs' = xs in map f xs)

fromStrictList : List a -> LazyList a
fromStrictList Nil = Nil
fromStrictList (x::xs) = x::(fromStrictList xs)

toStrictList : LazyList a -> List a
toStrictList (Delay Nil) = Nil
toStrictList (Delay (x::xs)) = x::(toStrictList xs)

countdown : Nat -> LazyList Nat
countdown Z = [Z]
countdown (S n) = (S n)::(countdown n)

take : Nat -> LazyList a -> LazyList a
take Z _ = Nil
take (S n) xs = Delay $
  case xs of
    Delay Nil => Nil
    Delay (x::xs') => x::(take n xs')

ack' : Nat -> Nat -> Nat
ack'    Z     m  = S m
ack' (S n)    Z  = ack' n (S Z)
ack' (S n) (S m) = ack' n (ack' (S n) m)

ack : Nat -> Nat
ack n = ack' n n

example : LazyList Nat
example = [1,2,3,4,5,6,7,8]

firstThreeAckValues : List Nat
firstThreeAckValues = toStrictList $ take 3 $ map ack example
