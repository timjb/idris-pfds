module Data.RealTimeQueue

import Data.Vect
import Data.So

-- adapted from Chris Okasaki's `Purely Functional Data Structures`, figure 7.1

%default total

data LazyVectCell : Nat -> Type -> Type where
  Nil  : LazyVectCell Z a
  (::) : (x : a) -> (xs : Lazy (LazyVectCell n a)) -> LazyVectCell (S n) a

LazyVect : Nat -> Type -> Type
LazyVect n a = Lazy (LazyVectCell n a)

fromStrictVect : Vect n a -> LazyVect n a
fromStrictVect Nil = Nil
fromStrictVect (x::xs) = x::(fromStrictVect xs)

lazyVectHead : LazyVect (S l) a -> a
lazyVectHead (x::xs) = x

-- (the strict implementation)
lazyVectTail : LazyVect (S l) a -> LazyVect l a
lazyVectTail (x::xs) = xs

twoNPlusM : Nat -> Nat -> Nat
twoNPlusM Z m = m
twoNPlusM (S n) m = S (twoNPlusM n (S m))

twoNPlusMCorrect : (n : Nat) -> (m : Nat) -> twoNPlusM n m = (n + (m + n))
twoNPlusMCorrect Z m = sym (plusZeroRightNeutral m)
twoNPlusMCorrect (S n) m =
  rewrite (twoNPlusMCorrect n (S m)) in
  rewrite (sym (plusSuccRightSucc m n)) in
  Refl


concatReverse' : LazyVect n a -> Vect (S n) a -> LazyVect m a -> LazyVect (S (twoNPlusM n m)) a
concatReverse' (Delay Nil) (y::Nil) a = y::a
concatReverse' (Delay (x::xs)) (y::ys) a = x::(concatReverse' xs ys (y::a))

concatReverse : LazyVect n a -> Vect (S n) a -> LazyVect (S (n + n)) a
concatReverse {n=n} xs ys = rewrite (sym (twoNPlusMCorrect n Z)) in concatReverse' xs ys (Delay Nil)

NatPair : Type
NatPair = (Nat, Nat)

data Queue' : NatPair -> Type -> Type where
  QueueC' : LazyVect (n + m) a -> Vect n a -> LazyVect m a -> Queue' (n, m) a

sucPair : NatPair -> NatPair
sucPair (n, Z)   = (Z, S (n + n))
sucPair (n, S m) = (S n, m)

twoNPlusMPair : NatPair -> Nat
twoNPlusMPair = uncurry twoNPlusM

sucPairCorrect : (p : NatPair) -> twoNPlusMPair (sucPair p) = S (twoNPlusMPair p)
sucPairCorrect (n, Z) =
  rewrite (twoNPlusMCorrect n Z) in
  Refl
sucPairCorrect (n, S m) = Refl

-- In the implementation of snoc', Idris doesn't accept 'rewrite … in xs'
-- If 'rewrite LazyVect … xs' is used, Idris is happy.
rewriteLazyVect : m = n -> LazyVect n a -> LazyVect m a
rewriteLazyVect eq vect = rewrite eq in vect

snoc' : Queue' p a -> a -> Queue' (sucPair p) a
snoc' {p=(n,Z)} (QueueC' xs ys Nil) v =
  let f' = concatReverse (rewriteLazyVect (sym (plusZeroRightNeutral n)) xs) (v::ys)
  in QueueC' f' Nil f'
snoc' {p=(n,S m)} (QueueC' xs ys (z::zs)) v =
  QueueC' (rewriteLazyVect (plusSuccRightSucc n m) xs) (v::ys) zs

pairSum : NatPair -> Nat
pairSum = uncurry (+)

pairNotZero : NatPair -> Bool
pairNotZero (Z, Z) = False
pairNotZero _ = True

PairNotZero : NatPair -> Type
PairNotZero = So . pairNotZero

pairNotZeroSumPositive : (p : NatPair) -> PairNotZero p -> (l : Nat ** pairSum p = S l)
pairNotZeroSumPositive (Z,Z) Oh impossible
pairNotZeroSumPositive (Z,S m) _ = (m ** Refl)
pairNotZeroSumPositive (S n,m) _ = ((n + m) ** Refl)

sumPositivePairNotZero : (p : NatPair) -> pairSum p = S l -> PairNotZero p
sumPositivePairNotZero {l=l} (Z,Z) Refl impossible
sumPositivePairNotZero (Z,S m) _ = Oh
sumPositivePairNotZero (S n,m) _ = Oh

twoNPlusMPositivePairNotZero : (p : NatPair) -> twoNPlusMPair p = S l -> PairNotZero p
twoNPlusMPositivePairNotZero {l=l} (Z,Z) Refl impossible
twoNPlusMPositivePairNotZero (Z,S m) _ = Oh
twoNPlusMPositivePairNotZero (S n,m) _ = Oh

head' : Queue' p a -> pairSum p = S l -> a
head' {l=l} (QueueC' xs _ _) eq =
  lazyVectHead {l} (rewrite (sym eq) in xs)

predPair : NatPair -> NatPair
predPair (n, S m) = (n, m)
predPair (Z, Z)   = (Z, Z)
predPair (S n, Z) = (Z, S (n + n))

predPairCorrect : (p : NatPair) -> twoNPlusMPair (predPair p) = pred (twoNPlusMPair p)
predPairCorrect (Z, Z) = Refl
predPairCorrect (S n, Z) =
  rewrite (twoNPlusMCorrect n 1) in
  rewrite (sym (plusSuccRightSucc n n)) in
  Refl
predPairCorrect (n, S m) =
  rewrite (twoNPlusMCorrect n (S m)) in
  rewrite (twoNPlusMCorrect n m) in
  rewrite (sym (plusSuccRightSucc n (m + n))) in
  Refl

tail' : Queue' p a -> PairNotZero p -> Queue' (predPair p) a
tail' {p=(n,S m)} (QueueC' xs ys (z::zs)) _ =
  let tl = lazyVectTail {l=(n+m)} (rewrite (plusSuccRightSucc n m) in xs)
  in QueueC' tl ys zs
tail' {p=(S n,Z)} (QueueC' xs ys Nil) _ =
  let tl = lazyVectTail {l=n} (rewrite (sym (plusZeroRightNeutral n)) in xs)
      f' = concatReverse tl ys
  in QueueC' f' Nil f'
tail' {p=(Z,Z)} _ Oh impossible


data Queue : Nat -> Type -> Type where
  QueueC : Queue' p a -> k = twoNPlusMPair p -> Queue k a

head : Queue (S l) a -> a
head {l=l} (QueueC {p=p} q eq) =
  let (k ** eq2) = pairNotZeroSumPositive p (twoNPlusMPositivePairNotZero {l=l} p (sym eq))
  in head' {l=k} q eq2

snoc : Queue l a -> a -> Queue (S l) a
snoc (QueueC {p=p} q eq) v = QueueC (snoc' q v) (trans (cong eq) (sym (sucPairCorrect p)))

tail : Queue (S l) a -> Queue l a
tail {l=l} (QueueC {p=p} q eq) =
  let pnz = twoNPlusMPositivePairNotZero {l=l} p (sym eq)
  in QueueC (tail' q pnz) (trans (cong eq) (sym (predPairCorrect p)))

toVect : Queue n a -> Vect n a
toVect {n=Z} _ = Nil
toVect {n=S n} q = (head q) :: (toVect (tail q))

fromVect : Vect n a -> Queue n a
fromVect xs =
  let f = fromStrictVect xs
  in QueueC (QueueC' f Nil f) Refl

