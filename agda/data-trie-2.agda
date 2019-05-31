-- module Agda.Builtin.Char

open import char
open import maybe
open import string
open import unit
open import level
open import eq
open import nat
open import nat-thms
open import bool
open import bool-thms
open import product
open import product-thms
open import neq
open import empty
open import list
open import list-thms
open import level



-- {-# BUILTIN CHAR char #-}

----------------------------------------------------------------------
-- primitive operations
----------------------------------------------------------------------

private
 primitive
  primCharToNat    : char → ℕ
  --primCharEquality : char → char → 𝔹



_<char2_ : char → char → 𝔹
_<char2_ c1 c2 = (primCharToNat c1) < (primCharToNat c2)




data Trie : 𝕃 char -> Set
data Link : 𝕃 char -> Set


--data LinkList : char → 𝕃 char → Set


-- {ℓ} (A : Set ℓ) : Set ℓ


{-
-- A proof that x is less than all values in xs
data _≤*_ (A : Set) : 𝕃 A → Set where
  []  : A ≤* []
  _::_ : ∀ {y ys} → (A ≤ y) → A ≤* ys → A ≤* (y :: ys)

-- Proof that a list is sorted
data IsSorted (A : Set) : 𝕃 A → Set where
  []  : IsSorted []
  _::_ : ∀ {x xs} → x ≤* xs → IsSorted xs → IsSorted (x :: xs)
-}

-- Sorted permutations of a list
{-
data Sorted {c} {l} : 𝕃 (Link c l) → Set  where
  []   : Sorted []
  cons : ∀ x {xs xxs}
       -- → (p : x ◂ xs ≡ xxs) -- inserting x somewhere into xs gives xxs
       → (least : x ≤* xs)  -- x is the smallest element of the list
       → (rest : Sorted xs) -- and we have also sorted xs
       → Sorted xxs
-}

{-

-- A proof that x is less than all values in xs
data _≤*_ {c} {l} (A : Link c l) : 𝕃 (Link c l) → Set where
  <[]  : A ≤* []
  _<::_ : ∀ {y ys} → (A link< y) → A ≤* ys → A ≤* (y :: ys)


-- Proof that a list is sorted
data IsSorted {c} {l} : 𝕃 (Link c l) → Set where
  s[]  : IsSorted []
  _s::_ : ∀ {x xs} → x ≤* xs → IsSorted xs → IsSorted (x :: xs)

-}

data _≤*_ {l} (x : Link l) : 𝕃 (Link l) → Set
data IsSorted {l} : 𝕃 (Link l) → Set

data Trie where
  node : ∀ {l : 𝕃 char} 
         → (wordp : bool)
         → (children : 𝕃 (Link l))
         → IsSorted children
         → Trie l

data Link where
  link : ∀ (c : char) { l : 𝕃 char }
         → (child : Trie (l ++ ( c :: [])))
         → Link l


_link<_ : ∀ {l : 𝕃 char} → Link l → Link l → 𝔹
_link<_ {l} (link c1 child1) (link c2 child2) = c1 <char2 c2


-- A proof that x is less than all values in xs
data _≤*_ {l} (x : Link l) where
  <[]  : x ≤* []
  _<::_ : ∀ {y ys} → (x link< y ≡ tt) → x ≤* ys → x ≤* (y :: ys)


-- Proof that a list is sorted
data IsSorted {l} where
  s[]  : IsSorted []
  _s::_ : ∀ {x xs} → x ≤* xs → IsSorted xs → IsSorted (x :: xs)



{-
data LinkList where
  ll[] : ∀ {c : char} → ∀ (l : 𝕃 char) → LinkList c l
d  _ll::_ : ∀ {l : 𝕃 char}
         → ∀ {c c' : char}
         → {c<c' : c <char c' ≡ tt}
      --   → Link l -- (child Trie (l ++  (c :: []))
         → Link c l
         → LinkList c' l
         → LinkList c l
-}

{-
data BST : ℕ -> ℕ -> Set where
  leaf : ∀ {n m} -> {n≤m : n ≤ m ≡ tt} -> BST n m
  node : ∀ {l' l u' u}
      -> (n : ℕ) -> (left : BST l' n) -> (right : BST n u')
      -> {l≤l' : l ≤ l' ≡ tt} -> {u'≤u : u' ≤ u ≡ tt}
      -> BST l u
-}

{-
sortedLinkTest : Link 'a' ('b' :: [])
sortedLinkTest = {!!}
-}

{-
testLinkList : LinkList 'a' ('b' :: []) ≡ LinkList 'a' ('b' :: [])
testLinkList = refl
-}

{-
list[] : ∀ {c : char} → (l : 𝕃 char) →  LinkList c l
list[] l = ll[] l
-}
-- cons : LinkList 'a' ('b' :: [])

{-
l1 : {c : char} → (l : 𝕃 char) → LinkList c l
l1 {c} l = (link c (node tt (LinkList c l))) ll:: ll[]
-}

--helper-lemma


t0 : Trie []
t0 = node ff [] s[]

t1 : Trie []
t1 = node tt [] s[]

t2 : Trie []
t2 = node ff (link 'a' (node tt [] s[]) :: []) (  <[] { [] } { (link 'a' (node tt [] s[])) } s:: s[])

t3 : Trie []
t3 = node ff
  (link 'a'
    (node tt [] s[]) ::
  (link 'o' (node ff
    (link 'n'
      (node tt [] s[]) :: [])
        (<[] {'o' :: []} {link 'n' ((node tt [] s[]) )} s:: s[])) :: []))
        ((refl <:: <[] {[]} {(link 'a' (node tt [] s[]))}) s:: (<[] {[]} {(link 'o' ((node ff ((link 'n' (node tt [] s[])) :: []) (<[] {'o' :: []} {link 'n' ((node tt [] s[]))} s:: s[]))))} s:: s[]))



{-
t3 : Trie []
t3 = node ff
 (link 'a' (node tt []) ::
 (link 'o' (node ff (link 'n' (node tt []) :: []))) ::
 [])
-}


-- (link 'a' (node tt [] s[])) s:: s[]

--t1 : ∀ {c : char} → Trie []
--t1 {c} = node tt (ll[] {c} [])

{-
t2 : ∀ {c : char} → Trie []
t2 {c} = node ff (link
                 'a'
                 (node tt
                       (ll[] ('a' :: []))) ll:: {[]} {'a' 'b'} { } {𝔹-contra} (ll[] []))

-}


{-
testLLCons : {'b' :: []} → {'b' 'a'} → {'a' <char 'b' ≡ tt} → (link 'a' ('b' :: [])) ll:: (LinkList 'b' ('b' :: []))
testLLCons = ?
-}


{-
testLLCons : (link 'a' {'b' :: []} (node ff ll[])) ll:: LinkList 'b' ('b' :: []) ≡ LinkList 'a' ('b' :: [])
testLLCons = ?
-}

{-
data List {a} (A : Set a) : Set a where
  []  : List A
  _::_ : (x : A) (xs : List A) → List A
-}



{- to compute all of the words in `t` -}
wordst : ∀ l -> (t : Trie l) -> 𝕃 (𝕃 char)

{- to compute all of the words in `lst`, which are the children of some Trie -}
wordsl : ∀ l -> (lst : 𝕃 (Link l)) -> 𝕃 (𝕃 char)


wordst l (node tt children proof) = l :: wordsl l children
wordst l (node ff children proof) = wordsl l children
wordsl l [] = []
wordsl l (link c child :: lt) =  (wordst (l ++ (c :: [])) child) ++ (wordsl l lt)

test0 : wordst [] t0 ≡ []
test0 = refl

test1 : wordst [] t1 ≡ [] :: []
test1 = refl

test2 : wordst [] t2 ≡ ('a' :: []) :: []
test2 = refl

test : wordst [] t3 ≡ ('a' :: [])  :: ('o' :: 'n' :: []) :: []
test = refl


