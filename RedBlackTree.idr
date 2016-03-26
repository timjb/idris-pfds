module Data.RedBlackTree

%default total
%access public export

-- BEWARE OF BUGS:
-- The totality checker in Idris is apparantly broken (as in version 0.9.20.2)
-- (found this bug while working on the code below: https://github.com/idris-lang/Idris-dev/issues/2884)


-- This is an adaptation of a Haskell-implementation of RB-trees by Stephanie Weirich
-- https://github.com/sweirich/dth/blob/master/examples/red-black/MightRedBlackGADT.hs


-- Implementation of deletion for red black trees by Matt Might
-- Editing to preserve the red/black tree invariants by Stephanie Weirich, 
-- Dan Licata and John Hughes

-- Original available from: 
--   http://matt.might.net/articles/red-black-delete/code/RedBlackSet.hs
-- Slides:
--   http://matt.might.net/papers/might2014redblack-talk.pdf

data C = R | B

implementation Eq C where
  R == R = True
  B == B = True
  _ == _ = False

implementation Show C where
  show R = "R"
  show B = "B"

cBlackHeight : C -> Nat
cBlackHeight R = 0
cBlackHeight B = 1

-- Well-formed Red/Black trees
-- n statically tracks the black height of the tree
-- c statically tracks the color of the root node
data CT : Nat -> C -> Type -> Type where
   E  : CT Z B a
   TR : CT n B  a -> a -> CT n B  a -> CT n R a
   TB : CT n c1 a -> a -> CT n c2 a -> CT (S n) B a

implementation Show a => Show (CT n c a) where
  show E = "E"
  show (TR a x b) =
    "(TR " ++ show a ++ " " ++ show x ++ " " ++ show b ++ ")"
  show (TB a x b) =
    "(TB " ++ show a ++ " " ++ show x ++ " " ++ show b ++ ")"

-- the top level type of red-black trees
-- the data constructor forces the root to be black and 
-- hides the black height.
data RBSet : Type -> Type where
  Root : CT n B a -> RBSet a
  
implementation Show a => Show (RBSet a) where
  show (Root t) = "(Root " ++ show t ++ ")"


 -- Public operations --

empty : RBSet a
empty = Root E

null : RBSet a -> Bool
null (Root E) = True
null _        = False

member : Ord a => a -> RBSet a -> Bool
member x (Root t) = aux x t
  where
    aux : Ord a => a -> CT n c a -> Bool
    aux x E = False
    aux x (TR l y r) =
      case compare x y of
        LT => aux x l
        GT => aux x r
        EQ => True
    aux x (TB l y r) =
      case compare x y of
        LT => aux x l
        GT => aux x r
        EQ => True

elements : RBSet a -> List a
elements (Root t) = aux t []
  where
    aux : CT n c a -> List a -> List a
    aux E acc = acc
    aux (TR a x b) acc = aux a (x :: aux b acc)
    aux (TB a x b) acc = aux a (x :: aux b acc)

 -- INSERTION --

-- an intermediate data structure that temporarily violates the 
-- red-black tree invariants during insertion. (IR stands for infra-red). 
-- This tree must be non-empty, but is allowed to have two red nodes in 
-- a row.
data IR : Nat -> Type -> Type where
   IN : (c : C) -> CT n c1 a -> a -> CT n c2 a -> IR (cBlackHeight c + n) a


-- `balance` rotates away coloring conflicts
-- we separate it into two cases based on whether the infraction could
-- be on the left or the right

bBalanceLeft : IR n a -> a -> CT n c1 a -> Exists (\c => CT (S n) c a)
bBalanceLeft (IN R (TR a x b) y c) z d      = Evidence R (TR (TB a x b) y (TB c z d))
bBalanceLeft (IN R a x (TR b y c)) z d      = Evidence R (TR (TB a x b) y (TB c z d))
bBalanceLeft (IN R {c1=B} {c2=B} a x b) z d = Evidence B (TB (TR a x b) z d)
bBalanceLeft (IN B a x b) z d               = Evidence B (TB (TB a x b) z d)

bBalanceRight : CT n c1 a -> a -> IR n a -> Exists (\c => CT (S n) c a)
bBalanceRight a x (IN R (TR b y c) z d)      = Evidence R (TR (TB a x b) y (TB c z d))
bBalanceRight a x (IN R b y (TR c z d))      = Evidence R (TR (TB a x b) y (TB c z d))
bBalanceRight a x (IN B b y d)               = Evidence B (TB a x (TB b y d))
bBalanceRight a x (IN R {c1=B} {c2=B} b y d) = Evidence B (TB a x (TR b y d))

insert : Ord a => a -> RBSet a -> RBSet a
insert x (Root s) = blacken (ins x s)
  where
    toIR : Exists (\c => CT (S n) c a) -> IR (S n) a
    toIR (Evidence R (TR a x b)) = IN R a x b
    toIR (Evidence B (TB a x b)) = IN B a x b
    mutual
      insB' : Ord a => {k:Nat} -> a -> (CT k c1 a, a, CT k c2 a) -> Exists (\c => CT (S k) c a)
      insB' x (a, y, b) =
        case compare x y of
          LT => bBalanceLeft (ins x a) y b
          GT => bBalanceRight a y (ins x b)
          EQ => Evidence B (TB a y b)
      insB : Ord a => {n:Nat} -> a -> CT n B a -> Exists (\c => CT n c a)
      insB {n=S m} x (TB a y b) = insB' {k=m} x (a, y, b)
      insB x E = Evidence R (TR E x E)
      ins : Ord a => a -> CT n c a -> IR n a
      ins x (TR a y b) =
        case compare x y of
          LT => let Evidence _ a' = insB x a in IN R a' y b
          GT => let Evidence _ b' = insB x b in IN R a y b'
          EQ => IN R a y b
      ins x (TB a y b) = toIR (insB' x (a, y, b))
      ins x E = IN R E x E
    blacken : IR n a -> RBSet a
    blacken (IN _ a x b) = Root (TB a x b)


 -- DELETION --
                                  

-- deletion tree, the result of del 
-- could have a double black node 
-- (but only at the top or as a single leaf)
data DTree : Nat -> Type -> Type where
  DT   : CT n c a -> DTree n a
  DTBB : CT n c1 a -> a -> CT n c2 a -> DTree (S (S n)) a
  DEE  : DTree (S Z) a

data RedTree : Nat -> Type -> Type where
  -- red tree
  RT  : CT n c1 a -> a -> CT n c2 a -> RedTree n a
  -- negative black tree
  NBT : CT (S n) B a -> a -> CT (S n) B a -> RedTree n a

data IR' : Nat -> Type -> Type where
   IN' : (c : C) -> CT n c1 a -> a -> CT n c2 a -> IR' (cBlackHeight c + n) a
   E' : IR' 0 a

toIR' : CT n c a -> IR' n a
toIR' E = E'
toIR' (TB a x b) = IN' B a x b
toIR' (TR a x b) = IN' R a x b

bbBalanceLeft : RedTree n a -> a -> CT n c1 a -> DTree (S (S n)) a
bbBalanceLeft (RT (TR a x b) y c) z d = DT (TB (TB a x b) y (TB c z d))
bbBalanceLeft (RT a x (TR b y c)) z d = DT (TB (TB a x b) y (TB c z d))
bbBalanceLeft (RT {c1=B} {c2=B} a x b) y c = DTBB (TR a x b) y c
bbBalanceLeft (NBT (TB a1 a2 a3) x (TB b y c)) z d =
  let Evidence _ leftTree = bBalanceLeft (IN R a1 a2 a3) x b
  in DT (TB leftTree y (TB c z d))

bbBalanceRight : CT n c1 a -> a -> RedTree n a -> DTree (S (S n)) a
bbBalanceRight a x (RT (TR b y c) z d) = DT (TB (TB a x b) y (TB c z d))
bbBalanceRight a x (RT b y (TR c z d)) = DT (TB (TB a x b) y (TB c z d))
bbBalanceRight a x (RT {c1=B} {c2=B} b y c) = DTBB a x (TR b y c)
bbBalanceRight a x (NBT (TB b y c) z (TB d1 d2 d3)) =
  let Evidence _ rightTree = bBalanceRight c z (IN R d1 d2 d3)
  in DT (TB (TB a x b) y rightTree)
  {-
      BB-x
       / \
      /   \
     a   NB-z
          / \
         /   \
       B-y  B-d
       / \
      /   \
     b     c
    
    will be transformed into
    
         B-y
         / \
        /   \
       /     \
      /       \
    B-x       B-z
    / \       / \
   /   \     /   \
  a     b   c    R-d <~ possible violation of invariants
  -}

rBubbleRight : CT n B a -> a -> DTree n a -> IR' n a
rBubbleRight a x (DT b) = IN' R a x b
rBubbleRight (TB a x b) y (DTBB c z d) =
  let Evidence _ t = bBalanceLeft (IN R a x b) y (TB c z d)
  in toIR' t
rBubbleRight (TB a x b) y DEE =
  let Evidence _ t = bBalanceLeft (IN R a x b) y E
  in toIR' t

bBubbleRight1 : CT n c1 a -> a -> DTree n a -> DTree (S n) a
bBubbleRight1 a x (DT b) = DT (TB a x b)
bBubbleRight1 (TB a x b) y (DTBB c z d) =
  bbBalanceLeft (RT a x b) y (TB c z d)
bBubbleRight1 (TB a x b) y DEE =
  bbBalanceLeft (RT a x b) y E
-- TODO: combine last two cases
bBubbleRight1 (TR a x b) y (DTBB c z d) =
  bbBalanceLeft (NBT a x b) y (TB c z d)
bBubbleRight1 (TR a x b) y DEE =
  bbBalanceLeft (NBT a x b) y E
-- TODO: combine last two cases
-- META-TODO: combine last four cases?

bBubbleRight2 : CT n c1 a -> a -> IR' n a -> DTree (S n) a
bBubbleRight2 a x (IN' color b y c) =
  let Evidence _ t = bBalanceRight a x (IN color b y c)
  in DT t
bBubbleRight2 a x E' = DT (TB a x E)

bBubbleRight : (c:C) -> CT n c1 a -> a ->
           (if c == R then IR' n a else DTree n a) ->
           DTree (S n) a
bBubbleRight R = bBubbleRight2
bBubbleRight B = bBubbleRight1

rBubbleLeft : DTree n a -> a -> CT n B a -> IR' n a
rBubbleLeft (DT a) x b = IN' R a x b
rBubbleLeft (DTBB a x b) y (TB c z d) =
  let Evidence _ t = bBalanceRight (TB a x b) y (IN R c z d)
  in toIR' t
rBubbleLeft DEE x (TB a y b) =
  let Evidence _ t = bBalanceRight E x (IN R a y b)
  in toIR' t

bBubbleLeft1 : DTree n a -> a -> CT n c1 a -> DTree (S n) a
bBubbleLeft1 (DT a) x b = DT (TB a x b)
bBubbleLeft1 (DTBB a x b) y (TB c z d) =
  bbBalanceRight (TB a x b) y (RT c z d)
bBubbleLeft1 DEE x (TB a y b) =
  bbBalanceRight E x (RT a y b)
-- TODO: combine last two cases
bBubbleLeft1 (DTBB a x b) y (TR c z d) =
  bbBalanceRight (TB a x b) y (NBT c z d)
bBubbleLeft1 DEE x (TR a y b) =
  bbBalanceRight E x (NBT a y b)
-- TODO: combine last two cases
-- META-TODO: combine last four cases?

bBubbleLeft2 : IR' n a -> a -> CT n c1 a -> DTree (S n) a
bBubbleLeft2 (IN' color a x b) y c =
  let Evidence _ t = bBalanceLeft (IN color a x b) y c
  in DT t
bBubbleLeft2 E' x a = DT (TB E x a)

bBubbleLeft : (c:C) -> (if c == R then IR' n a else DTree n a) ->
              a -> CT n c1 a ->
              DTree (S n) a
bBubbleLeft R = bBubbleLeft2
bBubbleLeft B = bBubbleLeft1

-- TODO: get rid of symmetric half?

-- maximum element from a red-black tree
max : (t:CT n c a) -> Maybe a
max E = Nothing
max (TB _ x E) = Just x
max (TR _ x E) = Just x
max (TB _ x r) = max r
max (TR _ x r) = max r

-- remove the maximum element of the tree
mutual
  rRemoveMax : CT n R a -> IR' n a
  rRemoveMax (TR E _ E) = E'
  rRemoveMax (TR a x b) = rBubbleRight a x (bRemoveMax b)
  bRemoveMax : CT n B a -> DTree n a
  bRemoveMax E = DT E
  bRemoveMax (TB E _ E) = DEE
  bRemoveMax (TB (TR a x b) _ E) = DT (TB a x b)
  bRemoveMax (TB {c2=d} a x b) = bBubbleRight d a x (removeMax b)
  removeMax : CT n c a -> (if c == R then IR' n a else DTree n a)
  removeMax {c=R} = rRemoveMax
  removeMax {c=B} = bRemoveMax

-- Remove the top node: it might leave behind a double black node
-- if the removed node is black (note that the height is preserved)
rRemove : CT n R a -> IR' n a
rRemove (TR E _ E) = E'
rRemove (TR a x b) = rBubbleLeft (bRemoveMax a) (fromMaybe x (max a)) b
-- here, `max l` is `Just x` for some `x:a` and `fromMaybe y (max l)` is simply `x`.

bRemove : CT n B a -> DTree n a
bRemove E = DT E
bRemove (TB E _ E) = DEE 
bRemove (TB E _ (TR a x b)) = DT (TB a x b)
bRemove (TB (TR a x b) _ E) = DT (TB a x b)
bRemove (TB {c1=d} a x b) = bBubbleLeft d (removeMax a) (fromMaybe x (max a)) b
-- here, `max l` is `Just x` for some `x:a` and `fromMaybe y (max l)` is simply `x`.

remove : CT n c a -> (if c == R then IR' n a else DTree n a)
remove {c=R} = rRemove
remove {c=B} = bRemove

-- like insert, delete relies on a helper function that may (slightly)
-- violate the red-black tree invariant

delete : Ord a => a -> RBSet a -> RBSet a
delete x (Root s) = del' x s
  where
    blackenCT : CT n c a -> RBSet a
    blackenCT E = Root E
    blackenCT (TR a x b) = Root (TB a x b)
    blackenCT (TB a x b) = Root (TB a x b)
    
    blackenDTree : DTree n a -> RBSet a
    blackenDTree (DT t) = blackenCT t
    blackenDTree DEE = Root E
    blackenDTree (DTBB a x b) = Root (TB a x b)
    
    blackenIR' : IR' n a -> RBSet a
    blackenIR' E' = Root E
    blackenIR' (IN' _ a x b) = Root (TB a x b)
    
    mutual
      rDel : Ord a => a -> CT n R a -> IR' n a
      rDel x (TR a y b) =
        case compare x y of
          LT => rBubbleLeft (bDel x a) y b
          GT => rBubbleRight a y (bDel x b)
          EQ => rRemove (TR a y b)
      bDel : Ord a => a -> CT n B a -> DTree n a
      bDel x E = DT E
      bDel x (TB {c1=d1} {c2=d2} a y b) =
        case compare x y of
          LT => bBubbleLeft d1 (del x a) y b
          GT => bBubbleRight d2 a y (del x b)
          EQ => bRemove (TB a y b)
      del : Ord a => a -> CT n c a -> (if c == R then IR' n a else DTree n a)
      del {c=R} = rDel
      del {c=B} = bDel
    
    del' : Ord a => a -> CT n c a -> RBSet a
    del' {c=R} x t = blackenIR' (rDel x t)
    del' {c=B} x t = blackenDTree (bDel x t)

-- TODO: proofs about properties
-- TODO: ordering invariant (maybe using https://personal.cis.strath.ac.uk/conor.mcbride/Pivotal.pdf)
