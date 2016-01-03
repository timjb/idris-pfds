module Data.RedBlackTree

import Data.So

%default total
%access public


-- This is an adaptation of a Haskell-implementation of RB-trees by Stephanie Weirich
-- https://github.com/sweirich/dth/blob/master/examples/red-black/MightRedBlackGADT.hs


-- Implementation of deletion for red black trees by Matt Might
-- Editing to preserve the red/black tree invariants by Stephanie Weirich, 
-- Dan Licata and John Hughes

-- Original available from: 
--   http://matt.might.net/articles/red-black-delete/code/RedBlackSet.hs
-- Slides:
--   http://matt.might.net/papers/might2014redblack-talk.pdf

{-
data Color = Red | Black | DoubleBlack | NegativeBlack

instance Show Color where
  show Red = "Red"
  show Black = "Black"
  show DoubleBlack = "DoubleBlack"
  show NegativeBlack = "NegativeBlack"

instance DecEq Color where
  decEq Red Red = Yes Refl
  decEq Black Black = Yes Refl
  decEq DoubleBlack DoubleBlack = Yes Refl
  decEq NegativeBlack NegativeBlack = Yes Refl
  decEq Red Black = No $ \Refl impossible
  decEq Red DoubleBlack = No $ \Refl impossible
  decEq Red NegativeBlack = No $ \Refl impossible
  decEq Black Red = No $ \Refl impossible
  decEq Black DoubleBlack = No $ \Refl impossible
  decEq Black NegativeBlack = No $ \Refl impossible
  decEq DoubleBlack Red = No $ \Refl impossible
  decEq DoubleBlack Black = No $ \Refl impossible
  decEq DoubleBlack NegativeBlack = No $ \Refl impossible
  decEq NegativeBlack Red = No $ \Refl impossible
  decEq NegativeBlack Black = No $ \Refl impossible
  decEq NegativeBlack DoubleBlack = No $ \Refl impossible
-}

data C = R | B

instance Eq C where
  R == R = True
  B == B = True
  _ == _ = False

instance Show C where
  show R = "R"
  show B = "B"

cBlackHeight : C -> Nat
cBlackHeight R = 0
cBlackHeight B = 1

valid : C -> C -> C -> Bool
valid R B B = True
valid B _ _ = True
valid _ _ _ = False

{-
-- this function forces the children of red nodes to be black
-- and also excludes double-black and negative-black nodes from
-- a valid red-black tree.
valid : Color -> Color -> Color -> Bool
valid Red Black Black = True
valid Black _ _ = True
valid _ _ _ = False

-- incrementing the black height, based on the color 
partial
bhIncr : Color -> Nat -> Nat
bhIncr Black n = S n
bhIncr DoubleBlack n = S (S n)
bhIncr Red n = n
bhIncr NegativeBlack (S n) = n
-}

-- Well-formed Red/Black trees
-- n statically tracks the black height of the tree
-- c statically tracks the color of the root node
data CT : Nat -> C -> Type -> Type where
   E  : CT Z B a
   {-
   T  : (c : C) -> {e : So (valid c c1 c2)} ->
        CT n c1 a -> a -> CT n c2 a -> CT (Data.RedBlackTree.bhIncr c n) c a
   -}
   TR : CT n B  a -> a -> CT n B  a -> CT n R a
   TB : CT n c1 a -> a -> CT n c2 a -> CT (S n) B a

instance Show a => Show (CT n c a) where
  show E = "E"
  show (TR l x r) =
    "(TR " ++ show l ++ " " 
          ++ show x ++ " " ++ show r ++ ")"
  show (TB l x r) =
    "(TB " ++ show l ++ " " 
          ++ show x ++ " " ++ show r ++ ")"

{-
ctFold : b -> (b -> a -> b -> b) -> CT n c a -> b
ctFold c f E = c
ctFold c f (TR l x r) = f (ctElim c f l) x (ctElim c f r)
ctFold c f (TB l x r) = f (ctElim c f l) x (ctElim c f r)
-}

-- the top level type of red-black trees
-- the data constructor forces the root to be black and 
-- hides the black height.
data RBSet : Type -> Type where
  Root : CT n B a -> RBSet a
  
instance Show a => Show (RBSet a) where
  show (Root x) = "Root (" ++ show x ++ ")"

{-
rbSetElim : s -> (RBSet a -> a -> RBSet a -> s) -> RBSet a -> s
rbSetElim c f (Root E) = c
rbSetElim c f (Root (TR l x r)) = f (Root l) x (Root r)
rbSetElim c f (Root (TB l x r)) = f (Root l) x (Root r)
-}

{-
showT : CT n c a -> String
showT E = "E"
showT (T c l x r) = 
    "(T " ++ show c ++ " " ++ showT l ++ " " 
          ++ "..." ++ " " ++ showT r ++ ")"
-}

{-
data ((a :: k) :~: (b :: k)) where
  Refl :: a :~: a
-}

{-
-- comparing two Red/Black trees for equality. 
-- unfortunately, because we have two instances, we can't
-- use the testEquality class.
(%==%) :: Eq a => CT n1 c1 a -> CT n2 c2 a -> Bool
E %==% E = True
T c1 a1 x1 b1 %==% T c2 a2 x2 b2 = 
  isJust (testEquality c1 c2) && a1 %==% a2 && x1 == x2 && b1 %==% b2
  
instance Eq a => Eq (RBSet a) where
  (Root t1) == (Root t2) = t1 %==% t2
-}


 -- Public operations --

empty : RBSet a
empty = Root E

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
   --INR : CT n c1 a -> a -> CT n c2 a -> IR n a
   --INB : CT n c1 a -> a -> CT n c2 a -> IR (S n) a


-- `balance` rotates away coloring conflicts
-- we separate it into two cases based on whether the infraction could
-- be on the left or the right

bBalanceL : IR n a -> a -> CT n c1 a -> Exists (\c => CT (S n) c a)
bBalanceL (IN R (TR a x b) y c) z d = Evidence R (TR (TB a x b) y (TB c z d))
bBalanceL (IN R a x (TR b y c)) z d = Evidence R (TR (TB a x b) y (TB c z d))
bBalanceL (IN B a x b) z d          = Evidence B (TB (TB a x b) z d)

partial
bBalanceR : CT n c1 a -> a -> IR n a -> Exists (\c => CT (S n) c a)
bBalanceR a x (IN R (TR b y c) z d) = Evidence R (TR (TB a x b) y (TB c z d))
bBalanceR a x (IN R b y (TR c z d)) = Evidence R (TR (TB a x b) y (TB c z d))
bBalanceR a x (IN B b z d)          = Evidence B (TB a x (TB b z d))

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
          LT => bBalanceL (ins x a) y b
          GT => bBalanceR a y (ins x b)
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
  --DT   : (c:C) -> CT n c1 a -> a -> CT n c2 a -> DTree (cBlackHeight c + n) a
  DT   : CT n c a -> DTree n a
  DTBB : CT n c1 a -> a -> CT n c2 a -> DTree (S (S n)) a
  DEE  : DTree (S Z) a
  
-- Note: we could unify this with the IR data structure by   
-- adding the DE and DEE data constructors. That would allow us to 
-- reuse the same balancing function (and blacken function) 
-- for both insertion and deletion. 
-- However, if an Agda version did that it might get into trouble, 
-- trying to show that insertion never produces a leaf.
  

{-
instance Show a => Show (DT n a) where
  show DE = "DE"
  show DEE = "DEE"
  show (DT c l x r) = 
    "(DT " ++ show c ++ " " ++ show l ++ " " 
           ++ "..." ++ " " ++ show r ++ ")"

-- Note: eliding a to make error easier below.
showDT :: DT n a -> String
showDT DE = "DE"
showDT DEE = "DEE"
showDT (DT c l x r) = 
    "(DT " ++ show c ++ " " ++ showT l ++ " " 
           ++ "..." ++ " " ++ showT r ++ ")"
-}

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

bbBalanceL : RedTree n a -> a -> CT n c1 a -> DTree (S (S n)) a
bbBalanceL (RT (TR a x b) y c) z d = DT (TB (TB a x b) y (TB c z d))
bbBalanceL (RT a x (TR b y c)) z d = DT (TB (TB a x b) y (TB c z d))
bbBalanceL (RT {c1=B} {c2=B} a x b) y c = DTBB (TR a x b) y c
bbBalanceL (NBT (TB a1 a2 a3) x (TB b y c)) z d =
  let Evidence _ leftTree = bBalanceL (IN R a1 a2 a3) x b
  in DT (TB leftTree y (TB c z d))

partial
bbBalanceR : CT n c1 a -> a -> RedTree n a -> DTree (S (S n)) a
bbBalanceR a x (RT (TR b y c) z d) = DT (TB (TB a x b) y (TB c z d))
bbBalanceR a x (RT b y (TR c z d)) = DT (TB (TB a x b) y (TB c z d))
bbBalanceR a x (RT {c1=B} {c2=B} b y c) = DTBB a x (TR b y c)
bbBalanceR a x (NBT (TB b y c) z (TB d1 d2 d3)) =
  let Evidence _ rightTree = bBalanceR c z (IN R d1 d2 d3)
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

rBubbleR : CT n B a -> a -> DTree n a -> IR' n a
rBubbleR a x (DT b) = IN' R a x b
rBubbleR (TB a x b) y (DTBB c z d) =
  let Evidence _ t = bBalanceL (IN R a x b) y (TB c z d)
  in toIR' t
rBubbleR (TB a x b) y DEE =
  let Evidence _ t = bBalanceL (IN R a x b) y E
  in toIR' t

bBubbleR1 : CT n c1 a -> a -> DTree n a -> DTree (S n) a
bBubbleR1 a x (DT b) = DT (TB a x b)
bBubbleR1 (TB a x b) y (DTBB c z d) =
  bbBalanceL (RT a x b) y (TB c z d)
bBubbleR1 (TB a x b) y DEE =
  bbBalanceL (RT a x b) y E
-- TODO: combine last two cases
bBubbleR1 (TR a x b) y (DTBB c z d) =
  bbBalanceL (NBT a x b) y (TB c z d)
bBubbleR1 (TR a x b) y DEE =
  bbBalanceL (NBT a x b) y E
-- TODO: combine last two cases
-- META-TODO: combine last four cases?

bBubbleR2 : CT n c1 a -> a -> IR' n a -> DTree (S n) a
bBubbleR2 a x (IN' color b y c) =
  let Evidence _ t = bBalanceR a x (IN color b y c)
  in DT t
bBubbleR2 a x E' = DT (TB a x E)

bBubbleR : (c:C) -> CT n c1 a -> a ->
           (if c == R then IR' n a else DTree n a) ->
           DTree (S n) a
bBubbleR R = bBubbleR2
bBubbleR B = bBubbleR1

rBubbleL : DTree n a -> a -> CT n B a -> IR' n a
rBubbleL (DT a) x b = IN' R a x b
rBubbleL (DTBB a x b) y (TB c z d) =
  let Evidence _ t = bBalanceR (TB a x b) y (IN R c z d)
  in toIR' t
rBubbleL DEE x (TB a y b) =
  let Evidence _ t = bBalanceR E x (IN R a y b)
  in toIR' t

bBubbleL1 : DTree n a -> a -> CT n c1 a -> DTree (S n) a
bBubbleL1 (DT a) x b = DT (TB a x b)
bBubbleL1 (DTBB a x b) y (TB c z d) =
  bbBalanceR (TB a x b) y (RT c z d)
bBubbleL1 DEE x (TB a y b) =
  bbBalanceR E x (RT a y b)
-- TODO: combine last two cases
bBubbleL1 (DTBB a x b) y (TR c z d) =
  bbBalanceR (TB a x b) y (NBT c z d)
bBubbleL1 DEE x (TR a y b) =
  bbBalanceR E x (NBT a y b)
-- TODO: combine last two cases
-- META-TODO: combine last four cases?

partial
bBubbleL2 : IR' n a -> a -> CT n c1 a -> DTree (S n) a
bBubbleL2 (IN' color a x b) y c =
  let Evidence _ t = bBalanceL (IN color a x b) y c
  in DT t
bBubbleL2 E' x a = DT (TB E x a)

bBubbleL : (c:C) -> (if c == R then IR' n a else DTree n a) ->
           a -> CT n c1 a ->
           DTree (S n) a
bBubbleL R = bBubbleL2
bBubbleL B = bBubbleL1

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
  rRemoveMax (TR a x b) = rBubbleR a x (bRemoveMax b)
  bRemoveMax : CT n B a -> DTree n a
  bRemoveMax E = DT E
  bRemoveMax (TB E _ E) = DEE
  bRemoveMax (TB (TR a x b) _ E) = DT (TB a x b)
  bRemoveMax (TB {c2=d} a x b) = bBubbleR d a x (removeMax b)
  removeMax : CT n c a -> (if c == R then IR' n a else DTree n a)
  removeMax {c=R} = rRemoveMax
  removeMax {c=B} = bRemoveMax

-- Remove the top node: it might leave behind a double black node
-- if the removed node is black (note that the height is preserved)
rRemove : CT n R a -> IR' n a
rRemove (TR E _ E) = E'
rRemove (TR a x b) = rBubbleL (bRemoveMax a) (fromMaybe x (max a)) b
-- here, `max l` is `Just x` for some `x:a` and `fromMaybe y (max l)` is simply `x`.

bRemove : CT n B a -> DTree n a
bRemove E = DT E
bRemove (TB E _ E) = DEE 
bRemove (TB E _ (TR a x b)) = DT (TB a x b)
bRemove (TB (TR a x b) _ E) = DT (TB a x b)
bRemove (TB {c1=d} a x b) = bBubbleL d (removeMax a) (fromMaybe x (max a)) b
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
          LT => rBubbleL (bDel x a) y b
          GT => rBubbleR a y (bDel x b)
          EQ => rRemove (TR a y b)
      bDel : Ord a => a -> CT n B a -> DTree n a
      bDel x E = DT E
      bDel x (TB {c1=d1} {c2=d2} a y b) =
        case compare x y of
          LT => bBubbleL d1 (del x a) y b
          GT => bBubbleR d2 a y (del x b)
          EQ => bRemove (TB a y b)
      del : Ord a => a -> CT n c a -> (if c == R then IR' n a else DTree n a)
      del {c=R} = rDel
      del {c=B} = bDel
    
    del' : Ord a => a -> CT n c a -> RBSet a
    del' {c=R} x t = blackenIR' (rDel x t)
    del' {c=B} x t = blackenDTree (bDel x t)

{-
--- Testing code

instance (Ord a, Arbitrary a) => Arbitrary (RBSet a)  where
  arbitrary = g where
    g :: forall a. (Ord a, Arbitrary a) => Gen (RBSet a)
    g = liftM (foldr insert empty) (arbitrary :: Gen [a])
       
prop_BST :: RBSet Int -> Bool
prop_BST t = isSortedNoDups (elements t)


isSortedNoDups :: Ord a => [a] -> Bool  
isSortedNoDups x = nub (sort x) == x
              
                            
prop_delete_spec1 :: RBSet Int -> Bool
prop_delete_spec1 t = all (\x -> not (member x (delete x t))) (elements t)

prop_delete_spec2 :: RBSet Int -> Bool
prop_delete_spec2 t = all (\(x,y) -> x == y || (member y (delete x t))) allpairs where
   allpairs = [ (x,y) | x <- elements t, y <- elements t ]


prop_delete_spec3 :: RBSet Int -> Int -> Property
prop_delete_spec3 t x = not (x `elem` elements t) ==> (delete x t == t)

prop_delete_bst :: RBSet Int -> Bool
prop_delete_bst t = all (\x -> prop_BST (delete x t)) (elements t)

check_insert = do
    putStrLn "BST property"
    quickCheck prop_BST


check_delete = do
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete_spec1
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete_spec2
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete_spec3
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete_bst
-}