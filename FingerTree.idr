module FingerTree

import Data.So

%default total
%access public export

-- A general sequence representation with arbitrary annotations, for
-- use as a base for implementations of various collection types, as
-- described in section 4 of
--
--    * Ralf Hinze and Ross Paterson,
--      \"Finger trees: a simple general-purpose data structure\",
--      /Journal of Functional Programming/ 16:2 (2006) pp 197-217.
--      <http://www.soi.city.ac.uk/~ross/papers/FingerTree.html>
--
-- This implementation was adapted with minimal changes from their Haskell
-- implementation, published as the `fingertree` library on Hackage.

{-
module Data.FingerTree (
#if TESTING
  FingerTree(..), Digit(..), Node(..), deep, node2, node3,
#else
  FingerTree,
#endif
  Measured(..),
  -- * Construction
  empty, singleton,
  (<|), (|>), (><),
  fromList,
  -- * Deconstruction
  null,
  ViewL(..), ViewR(..), viewl, viewr,
  split, takeUntil, dropUntil,
  -- * Transformation
  reverse,
  fmap', fmapWithPos, unsafeFmap,
  traverse', traverseWithPos, unsafeTraverse
  -- * Example
  -- $example
  ) where

import Prelude hiding (null, reverse)

import Control.Applicative (Applicative(pure, (<*>)), (<$>))
import Data.Monoid
import Data.Foldable (Foldable(foldMap), toList)
-}

infixr 5 <|, :<
infixl 5 |>, :>

infixr 5 ><

||| View of the left end of a sequence.
data ViewL : (Type -> Type) -> Type -> Type where
  EmptyL : ViewL s a -- ^ empty sequence
  (:<) : a -> s a -> ViewL s a -- ^ leftmost element and the rest of the sequence
  --deriving (Eq, Ord, Show, Read)

||| View of the right end of a sequence.
data ViewR : (Type -> Type) -> Type -> Type where
  EmptyR : ViewR s a -- ^ empty sequence
  (:>) : s a -> a -> ViewR s a -- ^ the sequence minus the rightmost element,
      -- and the rightmost element
  --deriving (Eq, Ord, Show, Read)

implementation Functor s => Functor (ViewL s) where
  map _ EmptyL    = EmptyL
  map f (x :< xs) = f x :< map f xs

implementation Functor s => Functor (ViewR s) where
  map _ EmptyR    = EmptyR
  map f (xs :> x) = map f xs :> f x

-- Explicit Digit type (Exercise 1)

data Digit a
  = One a
  | Two a a
  | Three a a a
  | Four a a a a

implementation Foldable Digit where
  foldr f acc (One a) = f a acc
  foldr f acc (Two a b) = f a (f b acc)
  foldr f acc (Three a b c) = f a (f b (f c acc))
  foldr f acc (Four a b c d) = f a (f b (f c (f d acc)))
  foldl f acc (One a) = f acc a
  foldl f acc (Two a b) = f (f acc a) b
  foldl f acc (Three a b c) = f (f (f acc a) b) c
  foldl f acc (Four a b c d) = f (f (f (f acc a) b) c) d

-------------------
-- 4.1 Measurements
-------------------

||| Things that can be measured.
interface Monoid v => Measured v a where
  measure : a -> v

implementation Measured v a => Measured v (Digit a) where
  measure = concatMap measure

---------------------------
-- 4.2 Caching measurements
---------------------------

data Node v a = Node2 v a a | Node3 v a a a

implementation Foldable (Node v) where
  foldr f acc (Node2 _ a b) = f a (f b acc)
  foldr f acc (Node3 _ a b c) = f a (f b (f c acc))
  foldl f acc (Node2 _ a b) = f (f acc a) b
  foldl f acc (Node3 _ a b c) = f (f (f acc a) b) c

node2 : Measured v a => a -> a -> Node v a
node2 a b = Node2 (measure a <+> measure b) a b

node3 : Measured v a => a -> a -> a -> Node v a
node3 a b c = Node3 (measure a <+> measure b <+> measure c) a b c

implementation Monoid v => Measured v (Node v a) where
  measure (Node2 v _ _)    =  v
  measure (Node3 v _ _ _)  =  v

nodeToDigit : Node v a -> Digit a
nodeToDigit (Node2 _ a b) = Two a b
nodeToDigit (Node3 _ a b c) = Three a b c

||| A representation of a sequence of values of type @a@, allowing
||| access to the ends in constant time, and append and split in time
||| logarithmic in the size of the smaller piece.
|||
||| The collection is also parameterized by a measure type @v@, which
||| is used to specify a position in the sequence for the 'split' operation.
||| The types of the operations enforce the constraint @'Measured' v a@,
||| which also implies that the type @v@ is determined by @a@.
|||
||| A variety of abstract data types can be implemented by using different
||| element types and measurements.
data FingerTree v a
  = Empty
  | Single a
  | Deep v (Digit a) (Lazy (FingerTree v (Node v a))) (Digit a)

ftMeasure : Measured v a => FingerTree v a -> v
ftMeasure Empty          = neutral
ftMeasure (Single x)     = measure x
ftMeasure (Deep v _ _ _) = v

||| /O(1)/. The cached measure of a tree.
implementation Measured v a => Measured v (FingerTree v a) where
  measure = ftMeasure

-- Avoid relying on right identity (cf Exercise 7)
mappendVal : Measured v a => v -> FingerTree v a -> v
mappendVal v Empty = v
mappendVal {a} v t = v <+> ftMeasure t

deep : Measured v a => 
   Digit a -> FingerTree v (Node v a) -> Digit a -> FingerTree v a
deep pr m sf = Deep ((measure pr `mappendVal` m) <+> measure sf) pr m sf

implementation Foldable (FingerTree v) where
  foldr _ acc Empty = acc
  foldr f acc (Single x) = f x acc
  foldr f acc (Deep _ pr (Delay m) sf) =
    foldr f (foldr (flip $ foldr f) (foldr f acc sf) m) pr
  foldl _ acc Empty = acc
  foldl f acc (Single x) = f acc x
  foldl f acc (Deep _ pr (Delay m) sf) =
    foldl f (foldl (foldl f) (foldl f acc pr) m) sf

implementation Eq a => Eq (FingerTree v a) where
  xs == ys = toList xs == toList ys

implementation Ord a => Ord (FingerTree v a) where
  compare xs ys = compare (toList xs) (toList ys)

mapNode : Measured v2 a2 =>
  (a1 -> a2) -> Node v1 a1 -> Node v2 a2
mapNode f (Node2 _ a b) = node2 (f a) (f b)
mapNode f (Node3 _ a b c) = node3 (f a) (f b) (f c)

mapDigit : (a -> b) -> Digit a -> Digit b
mapDigit f (One a) = One (f a)
mapDigit f (Two a b) = Two (f a) (f b)
mapDigit f (Three a b c) = Three (f a) (f b) (f c)
mapDigit f (Four a b c d) = Four (f a) (f b) (f c) (f d)

mapTree : Measured v2 a2 =>
  (a1 -> a2) -> FingerTree v1 a1 -> FingerTree v2 a2
mapTree _ Empty = Empty
mapTree f (Single x) = Single (f x)
mapTree f (Deep _ pr m sf) =
  deep (mapDigit f pr) (mapTree (mapNode f) m) (mapDigit f sf)

||| Like 'fmap', but with a more constrained type.
fmap' : (Measured v1 a1, Measured v2 a2) =>
  (a1 -> a2) -> FingerTree v1 a1 -> FingerTree v2 a2
fmap' = mapTree

mapWPNode : (Measured v1 a1, Measured v2 a2) =>
  (v1 -> a1 -> a2) -> v1 -> Node v1 a1 -> Node v2 a2
mapWPNode f v (Node2 _ a b) = node2 (f v a) (f va b)
  where va = v <+> measure a
mapWPNode f v (Node3 _ a b c) = node3 (f v a) (f va b) (f vab c)
  where va = v <+> measure a
        vab = va <+> measure b

mapWPDigit : Measured v a => (v -> a -> b) -> v -> Digit a -> Digit b
mapWPDigit f v (One a) = One (f v a)
mapWPDigit f v (Two a b) = Two (f v a) (f va b)
  where va = v <+> measure a
mapWPDigit f v (Three a b c) = Three (f v a) (f va b) (f vab c)
  where va = v <+> measure a
        vab = va <+> measure b
mapWPDigit f v (Four a b c d) = Four (f v a) (f va b) (f vab c) (f vabc d)
  where va = v <+> measure a
        vab = va <+> measure b
        vabc = vab <+> measure c

mapWPTree : (Measured v1 a1, Measured v2 a2) =>
  (v1 -> a1 -> a2) -> v1 -> FingerTree v1 a1 -> FingerTree v2 a2
mapWPTree _ _ Empty = Empty
mapWPTree f v (Single x) = Single (f v x)
mapWPTree f v (Deep _ pr m sf) =
  deep (mapWPDigit f v pr)
    (mapWPTree (mapWPNode f) vpr m)
    (mapWPDigit f vm sf)
  where vpr = v <+> measure pr
        vm = vpr  `mappendVal` m

||| Map all elements of the tree with a function that also takes the
||| measure of the prefix of the tree to the left of the element.
fmapWithPos : (Measured v1 a1, Measured v2 a2) =>
  (v1 -> a1 -> a2) -> FingerTree v1 a1 -> FingerTree v2 a2
fmapWithPos f = mapWPTree f neutral

unsafeFmapNode : (a -> b) -> Node v a -> Node v b
unsafeFmapNode f (Node2 v a b) = Node2 v (f a) (f b)
unsafeFmapNode f (Node3 v a b c) = Node3 v (f a) (f b) (f c)

||| Like 'fmap', but safe only if the function preserves the measure.
unsafeFmap : (a -> b) -> FingerTree v a -> FingerTree v b
unsafeFmap _ Empty = Empty
unsafeFmap f (Single x) = Single (f x)
unsafeFmap f (Deep v pr m sf) =
  Deep v (mapDigit f pr) (unsafeFmap (unsafeFmapNode f) m) (mapDigit f sf)

traverseNode : (Measured v2 a2, Applicative f) =>
  (a1 -> f a2) -> Node v1 a1 -> f (Node v2 a2)
traverseNode f (Node2 _ a b) = [| node2 (f a) (f b) |]
traverseNode f (Node3 _ a b c) = [| node3 (f a) (f b) (f c) |]

traverseDigit : Applicative f => (x -> f b) -> Digit x -> f (Digit b)
traverseDigit f (One a) = [| One (f a) |]
traverseDigit f (Two a b) = [| Two (f a) (f b) |]
traverseDigit f (Three a b c) = [| Three (f a) (f b) (f c) |]
traverseDigit f (Four a b c d) = [| Four (f a) (f b) (f c) (f d) |]

traverseTree : (Measured v2 a2, Applicative f) =>
  (a1 -> f a2) -> FingerTree v1 a1 -> f (FingerTree v2 a2)
traverseTree _ Empty = pure Empty
traverseTree f (Single x) = [| Single (f x) |]
traverseTree f (Deep _ pr m sf) =
  [| deep (traverseDigit f pr) (traverseTree (traverseNode f) m) (traverseDigit f sf) |]

||| Like 'traverse', but with a more constrained type.
traverse' : (Measured v1 a1, Measured v2 a2, Applicative f) =>
  (a1 -> f a2) -> FingerTree v1 a1 -> f (FingerTree v2 a2)
traverse' = traverseTree

traverseWPNode : (Measured v1 a1, Measured v2 a2, Applicative f) =>
  (v1 -> a1 -> f a2) -> v1 -> Node v1 a1 -> f (Node v2 a2)
traverseWPNode f v (Node2 _ a b) = [| node2 (f v a) (f va b) |]
  where va = v <+> measure a
traverseWPNode f v (Node3 _ a b c) = [| node3 (f v a) (f va b) (f vab c) |]
  where va  = v <+> measure a
        vab = va <+> measure b

traverseWPDigit : (Measured v a, Applicative f) =>
  (v -> a -> f b) -> v -> Digit a -> f (Digit b)
traverseWPDigit f v (One a) = [| One (f v a) |]
traverseWPDigit f v (Two a b) = [| Two (f v a) (f va b) |]
  where va  = v <+> measure a
traverseWPDigit f v (Three a b c) = [| Three (f v a) (f va b) (f vab c) |]
  where va  = v <+> measure a
        vab = va <+> measure b
traverseWPDigit f v (Four a b c d) = [| Four (f v a) (f va b) (f vab c) (f vabc d) |]
  where va   = v <+> measure a
        vab  = va <+> measure b
        vabc = vab <+> measure c

traverseWPTree : (Measured v1 a1, Measured v2 a2, Applicative f) =>
  (v1 -> a1 -> f a2) -> v1 -> FingerTree v1 a1 -> f (FingerTree v2 a2)
traverseWPTree _ _ Empty = pure Empty
traverseWPTree f v (Single x) = [| Single (f v x) |]
traverseWPTree f v (Deep _ pr m sf) =
  [| deep (traverseWPDigit f v pr) (traverseWPTree (traverseWPNode f) vpr m) (traverseWPDigit f vm sf) |]
  where vpr = v <+> measure pr
        vm = vpr `mappendVal` m

||| Traverse the tree with a function that also takes the
||| measure of the prefix of the tree to the left of the element.
traverseWithPos : (Measured v1 a1, Measured v2 a2, Applicative f) =>
  (v1 -> a1 -> f a2) -> FingerTree v1 a1 -> f (FingerTree v2 a2)
traverseWithPos f = traverseWPTree f neutral

unsafeTraverseNode : (Applicative f) =>
  (a -> f b) -> Node v a -> f (Node v b)
unsafeTraverseNode f (Node2 v a b) = Node2 v <$> f a <*> f b
unsafeTraverseNode f (Node3 v a b c) = Node3 v <$> f a <*> f b <*> f c

||| Like 'traverse', but safe only if the function preserves the measure.
unsafeTraverse : (Applicative f) =>
  (a -> f b) -> FingerTree v a -> f (FingerTree v b)
unsafeTraverse _ Empty = pure Empty
unsafeTraverse f (Single x) = [| Single (f x) |]
unsafeTraverse f (Deep v pr m sf) =
  Deep v <$> traverseDigit f pr <*> map Delay (unsafeTraverse (unsafeTraverseNode f) m) <*> traverseDigit f sf


-----------------------------------------------------
-- 4.3 Construction, deconstruction and concatenation
-----------------------------------------------------

||| /O(1)/. The empty sequence.
empty : Measured v a => FingerTree v a
empty = Empty

||| /O(1)/. A singleton sequence.
singleton : Measured v a => a -> FingerTree v a
singleton = Single

||| /O(1)/. Add an element to the left end of a sequence.
||| Mnemonic: a triangle with the single element at the pointy end.
(<|) : (Measured v a) => a -> FingerTree v a -> FingerTree v a
a <| Empty = Single a
a <| (Single b) = deep (One a) Empty (One b)
a <| (Deep v pr m sf) =
  case pr of
    One   b       => Deep (measure a <+> v) (Two   a b)     m sf
    Two   b c     => Deep (measure a <+> v) (Three a b c)   m sf
    Three b c d   => Deep (measure a <+> v) (Four  a b c d) m sf
    Four  b c d e => Deep (measure a <+> v) (Two a b) (node3 c d e <| m) sf

||| /O(n)/. Create a sequence from a finite list of elements.
fromList : (Measured v a) => List a -> FingerTree v a 
fromList = foldr (<|) Empty

||| /O(1)/. Add an element to the right end of a sequence.
||| Mnemonic: a triangle with the single element at the pointy end.
(|>) : (Measured v a) => FingerTree v a -> a -> FingerTree v a
Empty |> a = Single a
(Single a) |> b = deep (One a) Empty (One b)
(Deep v pr m sf) |> x =
  case sf of
    One   a       => Deep (v <+> measure x) pr m (Two a x)
    Two   a b     => Deep (v <+> measure x) pr m (Three a b x)
    Three a b c   => Deep (v <+> measure x) pr m (Four a b c x)
    Four  a b c d => Deep (v <+> measure x) pr (m |> node3 a b c) (Two d x)

||| /O(1)/. Is this the empty sequence?
null : (Measured v a) => FingerTree v a -> Bool
null Empty = True
null _ = False

digitToTree : (Measured v a) => Digit a -> FingerTree v a
digitToTree (One a) = Single a
digitToTree (Two a b) = deep (One a) Empty (One b)
digitToTree (Three a b c) = deep (Two a b) Empty (One c)
digitToTree (Four a b c d) = deep (Two a b) Empty (Two c d)

mutual
  ||| /O(1)/. Analyse the left end of a sequence.
  viewl : (Measured v a) => FingerTree v a -> ViewL (FingerTree v) a
  viewl Empty = EmptyL
  viewl (Single x) = x :< Empty
  viewl (Deep _ (One x) m sf) = x :< rotL m sf
  viewl (Deep _ (Two a b) m sf) = a :< deep (One b) m sf
  viewl (Deep _ (Three a b c) m sf) = a :< deep (Two b c) m sf
  viewl (Deep _ (Four a b c d) m sf) = a :< deep (Three a b c) m sf

  rotL : (Measured v a) => FingerTree v (Node v a) -> Digit a -> FingerTree v a
  rotL m sf = case viewl m of
    EmptyL  => digitToTree sf
    a :< m' => Deep (measure m <+> measure sf) (nodeToDigit a) m' sf

mutual
  ||| /O(1)/. Analyse the right end of a sequence.
  viewr : (Measured v a) => FingerTree v a -> ViewR (FingerTree v) a
  viewr Empty = EmptyR
  viewr (Single x) = Empty :> x
  viewr (Deep _ pr m (One a)) = rotR pr m :> a
  viewr (Deep _ pr m (Two a b)) = deep pr m (One a) :> b
  viewr (Deep _ pr m (Three a b c)) = deep pr m (Two a b) :> c
  viewr (Deep _ pr m (Four a b c d)) = deep pr m (Three a b c) :> d

  rotR : (Measured v a) => Digit a -> FingerTree v (Node v a) -> FingerTree v a
  rotR pr m = case viewr m of
    EmptyR  => digitToTree pr
    m' :> a => Deep (measure pr `mappendVal` m) pr m' (nodeToDigit a)

----------------
-- Concatenation
----------------

mutual
  addDigits2 : (Measured v a) => FingerTree v (Node v a) -> Digit a -> a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
  addDigits2 m1 (One a) b c (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits2 m1 (One a) b c (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits2 m1 (One a) b c (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits2 m1 (One a) b c (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Two a b) c d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits2 m1 (Two a b) c d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits2 m1 (Two a b) c d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Two a b) c d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits2 m1 (Three a b c) d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits2 m1 (Three a b c) d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Three a b c) d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits2 m1 (Three a b c) d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits2 m1 (Four a b c d) e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Four a b c d) e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits2 m1 (Four a b c d) e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits2 m1 (Four a b c d) e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2

  appendTree2 : (Measured v a) => FingerTree v a -> a -> a -> FingerTree v a -> FingerTree v a
  appendTree2 Empty a b xs =
    a <| b <| xs
  appendTree2 xs a b Empty =
    xs |> a |> b
  appendTree2 (Single x) a b xs =
    x <| a <| b <| xs
  appendTree2 xs a b (Single x) =
    xs |> a |> b |> x
  appendTree2 (Deep _ pr1 m1 sf1) a b (Deep _ pr2 m2 sf2) =
    deep pr1 (addDigits2 m1 sf1 a b pr2 m2) sf2

  addDigits3 : (Measured v a) => FingerTree v (Node v a) -> Digit a -> a -> a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
  addDigits3 m1 (One a) b c d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits3 m1 (One a) b c d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits3 m1 (One a) b c d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits3 m1 (One a) b c d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Two a b) c d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits3 m1 (Two a b) c d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits3 m1 (Two a b) c d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Two a b) c d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits3 m1 (Three a b c) d e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits3 m1 (Three a b c) d e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Three a b c) d e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits3 m1 (Three a b c) d e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits3 m1 (Four a b c d) e f g (One h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Four a b c d) e f g (Two h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits3 m1 (Four a b c d) e f g (Three h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits3 m1 (Four a b c d) e f g (Four h i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2

  appendTree3 : (Measured v a) => FingerTree v a -> a -> a -> a -> FingerTree v a -> FingerTree v a
  appendTree3 Empty a b c xs =
    a <| b <| c <| xs
  appendTree3 xs a b c Empty =
    xs |> a |> b |> c
  appendTree3 (Single x) a b c xs =
    x <| a <| b <| c <| xs
  appendTree3 xs a b c (Single x) =
    xs |> a |> b |> c |> x
  appendTree3 (Deep _ pr1 m1 sf1) a b c (Deep _ pr2 m2 sf2) =
    deep pr1 (addDigits3 m1 sf1 a b c pr2 m2) sf2

  addDigits4 : (Measured v a) => FingerTree v (Node v a) -> Digit a -> a -> a -> a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
  addDigits4 m1 (One a) b c d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits4 m1 (One a) b c d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits4 m1 (One a) b c d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits4 m1 (One a) b c d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Two a b) c d e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits4 m1 (Two a b) c d e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits4 m1 (Two a b) c d e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Two a b) c d e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits4 m1 (Three a b c) d e f g (One h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits4 m1 (Three a b c) d e f g (Two h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Three a b c) d e f g (Three h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits4 m1 (Three a b c) d e f g (Four h i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
  addDigits4 m1 (Four a b c d) e f g h (One i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Four a b c d) e f g h (Two i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits4 m1 (Four a b c d) e f g h (Three i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
  addDigits4 m1 (Four a b c d) e f g h (Four i j k l) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) m2

  appendTree4 : (Measured v a) => FingerTree v a -> a -> a -> a -> a -> FingerTree v a -> FingerTree v a
  appendTree4 Empty a b c d xs =
    a <| b <| c <| d <| xs
  appendTree4 xs a b c d Empty =
    xs |> a |> b |> c |> d
  appendTree4 (Single x) a b c d xs =
    x <| a <| b <| c <| d <| xs
  appendTree4 xs a b c d (Single x) =
    xs |> a |> b |> c |> d |> x
  appendTree4 (Deep _ pr1 m1 sf1) a b c d (Deep _ pr2 m2 sf2) =
    deep pr1 (addDigits4 m1 sf1 a b c d pr2 m2) sf2

mutual
  addDigits1 : (Measured v a) => FingerTree v (Node v a) -> Digit a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
  addDigits1 m1 (One a) b (One c) m2 =
    appendTree1 m1 (node3 a b c) m2
  addDigits1 m1 (One a) b (Two c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits1 m1 (One a) b (Three c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits1 m1 (One a) b (Four c d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Two a b) c (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits1 m1 (Two a b) c (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits1 m1 (Two a b) c (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Two a b) c (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits1 m1 (Three a b c) d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits1 m1 (Three a b c) d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Three a b c) d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits1 m1 (Three a b c) d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits1 m1 (Four a b c d) e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Four a b c d) e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits1 m1 (Four a b c d) e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits1 m1 (Four a b c d) e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2

  appendTree1 : (Measured v a) => FingerTree v a -> a -> FingerTree v a -> FingerTree v a
  appendTree1 Empty a xs =
    a <| xs
  appendTree1 xs a Empty =
    xs |> a
  appendTree1 (Single x) a xs =
    x <| a <| xs
  appendTree1 xs a (Single x) =
    xs |> a |> x
  appendTree1 (Deep _ pr1 m1 sf1) a (Deep _ pr2 m2 sf2) =
    deep pr1 (addDigits1 m1 sf1 a pr2 m2) sf2

addDigits0 : (Measured v a) => FingerTree v (Node v a) -> Digit a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
addDigits0 m1 (One a) (One b) m2 =
  appendTree1 m1 (node2 a b) m2
addDigits0 m1 (One a) (Two b c) m2 =
  appendTree1 m1 (node3 a b c) m2
addDigits0 m1 (One a) (Three b c d) m2 =
  appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (One a) (Four b c d e) m2 =
  appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Two a b) (One c) m2 =
  appendTree1 m1 (node3 a b c) m2
addDigits0 m1 (Two a b) (Two c d) m2 =
  appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (Two a b) (Three c d e) m2 =
  appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Two a b) (Four c d e f) m2 =
  appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Three a b c) (One d) m2 =
  appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (Three a b c) (Two d e) m2 =
  appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Three a b c) (Three d e f) m2 =
  appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Three a b c) (Four d e f g) m2 =
  appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits0 m1 (Four a b c d) (One e) m2 =
  appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Four a b c d) (Two e f) m2 =
  appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Four a b c d) (Three e f g) m2 =
  appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits0 m1 (Four a b c d) (Four e f g h) m2 =
  appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2

appendTree0 : (Measured v a) => FingerTree v a -> FingerTree v a -> FingerTree v a
appendTree0 Empty xs = xs
appendTree0 xs Empty = xs
appendTree0 (Single x) xs = x <| xs
appendTree0 xs (Single x) = xs |> x
appendTree0 (Deep _ pr1 m1 sf1) (Deep _ pr2 m2 sf2) =
  deep pr1 (addDigits0 m1 sf1 pr2 m2) sf2

||| /O(log(min(n1,n2)))/. Concatenate two sequences.
(><) : (Measured v a) => FingerTree v a -> FingerTree v a -> FingerTree v a
(><) =  appendTree0

Measured v a => Semigroup (FingerTree v a) where
  (<+>) = appendTree0

Measured v a => Monoid (FingerTree v a) where
  neutral = empty

----------------
-- 4.4 Splitting
----------------

data Splitting t a = Split t a t

splitNode : (Measured v a) => (v -> Bool) -> v -> Node v a ->
    Splitting (Maybe (Digit a)) a
splitNode p i (Node2 _ a b) =
  if p va then Split Nothing a (Just (One b))
          else Split (Just (One a)) b Nothing
  where va  = i <+> measure a
splitNode p i (Node3 _ a b c) =
  if p va then Split Nothing a (Just (Two b c))
  else if p vab then Split (Just (One a)) b (Just (One c))
  else Split (Just (Two a b)) c Nothing
  where va  = i <+> measure a
        vab = va <+> measure b

splitDigit : (Measured v a) => (v -> Bool) -> v -> Digit a ->
    Splitting (Maybe (Digit a)) a
splitDigit _ i (One a) = Split Nothing a Nothing
splitDigit p i (Two a b) =
  if p va then Split Nothing a (Just (One b))
          else Split (Just (One a)) b Nothing
  where va = i <+> measure a
splitDigit p i (Three a b c) =
  if p va then Split Nothing a (Just (Two b c))
  else if p vab then Split (Just (One a)) b (Just (One c))
  else Split (Just (Two a b)) c Nothing
  where va  = i <+> measure a
        vab = va <+> measure b
splitDigit p i (Four a b c d) =
  if p va then Split Nothing a (Just (Three b c d))
  else if p vab then Split (Just (One a)) b (Just (Two c d))
  else if p vabc then Split (Just (Two a b)) c (Just (One d))
  else Split (Just (Three a b c)) d Nothing
  where va   = i <+> measure a
        vab  = va <+> measure b
        vabc = vab <+> measure c

deepL : (Measured v a) =>
  Maybe (Digit a) -> FingerTree v (Node v a) -> Digit a -> FingerTree v a
deepL Nothing m sf   = rotL m sf
deepL (Just pr) m sf = deep pr m sf

deepR : (Measured v a) =>
  Digit a -> FingerTree v (Node v a) -> Maybe (Digit a) -> FingerTree v a
deepR pr m Nothing   = rotR pr m
deepR pr m (Just sf) = deep pr m sf

notEmpty : FingerTree v a -> Bool
notEmpty Empty = False
notEmpty _     = True

splitTree :  (Measured v a) => 
    (v -> Bool) -> v -> (t : FingerTree v a) -> So (notEmpty t) -> Splitting (FingerTree v a) a
splitTree _ _ Empty Oh impossible --so = absurd so --illegal_argument "splitTree"
splitTree _ _ (Single x) _ = Split Empty x Empty
splitTree p i (Deep _ pr m sf) _ =
  let vpr = i <+> measure pr in
  let vm = vpr `mappendVal` m in
  if p vpr then
    let Split l x r = splitDigit p i pr
    in Split (maybe Empty digitToTree l) x (deepL r m sf)
  else
    case (choose (notEmpty m), p vm) of
      (Left so, True) =>
        let Split ml xs mr = splitTree p vpr m so
            Split l x r = splitNode p (vpr `mappendVal` ml) xs
        in Split (deepR pr ml l) x (deepL r mr sf)
      _ =>
        let Split l x r =  splitDigit p vm sf
        in Split (deepR pr m l) x (maybe Empty digitToTree r)

||| /O(log(min(i,n-i)))/. Split a sequence at a point where the predicate
||| on the accumulated measure changes from 'False' to 'True'.
|||
||| For predictable results, one should ensure that there is only one such
||| point, i.e. that the predicate is /monotonic/.
split : (Measured v a) => 
          (v -> Bool) -> FingerTree v a -> (FingerTree v a, FingerTree v a)
split p xs =
  case choose (notEmpty xs) of
    Right _  => (Empty, Empty)
    Left  so =>
      let Split l x r = splitTree p neutral xs so
      in if p (measure xs) then (l, x <| r) else (xs, Empty)

||| /O(log(min(i,n-i)))/.
||| Given a monotonic predicate @p@, @'takeUntil' p t@ is the largest
||| prefix of @t@ whose measure does not satisfy @p@.
|||
||| *  @'takeUntil' p t = 'fst' ('split' p t)@
takeUntil : (Measured v a) => (v -> Bool) -> FingerTree v a -> FingerTree v a
takeUntil p = fst . split p

||| /O(log(min(i,n-i)))/.
||| Given a monotonic predicate @p@, @'dropUntil' p t@ is the rest of @t@
||| after removing the largest prefix whose measure does not satisfy @p@.
|||
||| * @'dropUntil' p t = 'snd' ('split' p t)@
dropUntil : (Measured v a) => (v -> Bool) -> FingerTree v a -> FingerTree v a
dropUntil p = snd . split p

------------------
-- Transformations
------------------

reverseDigit : (a -> b) -> Digit a -> Digit b
reverseDigit f (One a) = One (f a)
reverseDigit f (Two a b) = Two (f b) (f a)
reverseDigit f (Three a b c) = Three (f c) (f b) (f a)
reverseDigit f (Four a b c d) = Four (f d) (f c) (f b) (f a)

reverseNode : (Measured v2 a2) => (a1 -> a2) -> Node v1 a1 -> Node v2 a2
reverseNode f (Node2 _ a b) = node2 (f b) (f a)
reverseNode f (Node3 _ a b c) = node3 (f c) (f b) (f a)

reverseTree : (Measured v2 a2) => (a1 -> a2) -> FingerTree v1 a1 -> FingerTree v2 a2
reverseTree _ Empty = Empty
reverseTree f (Single x) = Single (f x)
reverseTree f (Deep _ pr m sf) =
  deep (reverseDigit f sf) (reverseTree (reverseNode f) m) (reverseDigit f pr)

||| /O(n)/. The reverse of a sequence.
reverse : (Measured v a) => FingerTree v a -> FingerTree v a
reverse = reverseTree id

{- $example

Particular abstract data types may be implemented by defining
element types with suitable 'Measured' implementations.

(from section 4.5 of the paper)
Simple sequences can be implemented using a 'Sum' monoid as a measure:

> newtype Elem a = Elem { getElem : a }
>
> implementation Measured (Sum Int) (Elem a) where
>     measure (Elem _) = Sum 1
>
> newtype Seq a = Seq (FingerTree (Sum Int) (Elem a))

Then the measure of a subsequence is simply its length.
This representation supports log-time extraction of subsequences:

> take : Int -> Seq a -> Seq a
> take k (Seq xs) = Seq (takeUntil (> Sum k) xs)
>
> drop : Int -> Seq a -> Seq a
> drop k (Seq xs) = Seq (dropUntil (> Sum k) xs)

The module @Data.Sequence@ is an optimized instantiation of this type.

For further examples, see "Data.IntervalMap.FingerTree" and
"Data.PriorityQueue.FingerTree".

-}
