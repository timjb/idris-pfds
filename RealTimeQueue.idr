module Data.RealTimeQueue

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
  let inductiveHypothesis = twoNPlusMCorrect n (S m)
  in ?twoNPlusMCorrectStepCase

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
sucPairCorrect (n, Z) = ?sucPairCorrectCase1
sucPairCorrect (n, S m) = refl

snoc' : Queue' p a -> a -> Queue' (sucPair p) a
snoc' {p=(n,Z)} (QueueC' xs ys Nil) v =
  let f' = concatReverse (rewrite (sym (plusZeroRightNeutral n)) in xs) (v::ys)
  in QueueC' f' Nil f'
snoc' {p=(n,S m)} (QueueC' xs ys (z::zs)) v =
  QueueC' (rewrite (plusSuccRightSucc n m) in xs) (v::ys) zs

pairSum : NatPair -> Nat
pairSum = uncurry (+)

pairNotZero : NatPair -> Bool
pairNotZero (Z, Z) = False
pairNotZero _ = True

PairNotZero : NatPair -> Type
PairNotZero = so . pairNotZero

pairNotZeroSumPositive : (p : NatPair) -> PairNotZero p -> (l : Nat ** pairSum p = S l)
pairNotZeroSumPositive (Z,Z) oh impossible
pairNotZeroSumPositive (Z,S m) _ = (m ** refl)
pairNotZeroSumPositive (S n,m) _ = ((n + m) ** refl)

sumPositivePairNotZero : (p : NatPair) -> pairSum p = S l -> PairNotZero p
sumPositivePairNotZero {l=l} (Z,Z) refl impossible
sumPositivePairNotZero (Z,S m) _ = oh
sumPositivePairNotZero (S n,m) _ = oh

twoNPlusMPositivePairNotZero : (p : NatPair) -> twoNPlusMPair p = S l -> PairNotZero p
twoNPlusMPositivePairNotZero {l=l} (Z,Z) refl impossible
twoNPlusMPositivePairNotZero (Z,S m) _ = oh
twoNPlusMPositivePairNotZero (S n,m) _ = oh

head' : Queue' p a -> pairSum p = S l -> a
head' {l=l} (QueueC' xs _ _) eq =
  lazyVectHead {l} (rewrite (sym eq) in xs)

predPair : NatPair -> NatPair
predPair (n, S m) = (n, m)
predPair (Z, Z)   = (Z, Z)
predPair (S n, Z) = (Z, S (n + n))

predPairCorrect : (p : NatPair) -> twoNPlusMPair (predPair p) = pred (twoNPlusMPair p)
predPairCorrect (Z, Z) = refl
predPairCorrect (S n, Z) = ?predPairCorrectCase1
predPairCorrect (n, S m) = ?predPairCorrectCase2

tail' : Queue' p a -> PairNotZero p -> Queue' (predPair p) a
tail' {p=(n,S m)} (QueueC' xs ys (z::zs)) _ =
  let tl = lazyVectTail {l=(n+m)} (rewrite (plusSuccRightSucc n m) in xs)
  in QueueC' tl ys zs
tail' {p=(S n,Z)} (QueueC' xs ys Nil) _ =
  let tl = lazyVectTail {l=n} (rewrite (sym (plusZeroRightNeutral n)) in xs)
      f' = concatReverse tl ys
  in QueueC' f' Nil f'
tail' {p=(Z,Z)} _ oh impossible


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
  in QueueC (QueueC' f Nil f) refl


------------------------------------------------------------------------------
-- Proofs
------------------------------------------------------------------------------

twoNPlusMCorrectStepCase = proof {
  intros;
  rewrite (sym inductiveHypothesis);
  rewrite (plusSuccRightSucc m n)
  trivial;
}

sucPairCorrectCase1 = proof {
  intros;
  rewrite (sym (twoNPlusMCorrect n Z));
  rewrite (sym (plusZeroRightNeutral n));
  rewrite (sym (plusZeroRightNeutral (n + n)));
  trivial;
}

predPairCorrectCase1 = proof {
  intros;
  rewrite (sym (twoNPlusMCorrect n 1));
  rewrite (plusSuccRightSucc n n);
  trivial;
}

predPairCorrectCase2 = proof {
  intros;
  rewrite (twoNPlusMCorrect n (S m));
  rewrite (sym (twoNPlusMCorrect n (S m)));
  rewrite (sym (twoNPlusMCorrect n m));
  rewrite (plusSuccRightSucc n (m + n));
  trivial;
}

