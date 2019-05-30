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


-- define bottom char where all chars are less than this...
{-
data BottomC : char where
  bottom : BottomC
  [[_]] : char → BottomC
-}

--this wont work because you can't put "bottom" in a link list since it takes a char
--<bottom : ∀ (c : char) → BottomC 
--<bottom = {!!}

{-
<bottom : ∀ (c : char) → BottomC <char c ≡ tt
<bottom = ?
-}

data SingletonList : 𝕃 char → Set where
  slist : ∀ {l : 𝕃 char}
          → {length l =N 1 ≡ tt}
          → SingletonList l

<SingletonChar : ∀ {c1 c2 : char} → c1 → c2 → 𝔹
<SingletonChar {c1} {c2} sl1 sl2 = {!!}


data Trie : 𝕃 char -> Set
data Link : 𝕃 char -> Set
data LinkList : char → 𝕃 char → Set

-- link-list of links
data Trie where
  node : ∀ {l : 𝕃 char} → ∀ {c : char} 
         → (wordp : bool)
         → (children : LinkList c l)
         → Trie l

data Link where
  link : ∀ (c : char) { l : 𝕃 char }
         → (child : Trie (l ++ ( c :: [])))
         → Link l

data LinkList where
  ll[] : ∀ (c : char) → ∀ (l : 𝕃 char) → LinkList c l
  _ll::_ : ∀ {l : 𝕃 char}
         → ∀ {c c' : char}
         → {c<c' : c <char c' ≡ tt}
         → Link l -- (child Trie (l ++  (c :: []))
         → LinkList c' l
         → LinkList c l



testLinkList : LinkList 'a' ('b' :: []) ≡ LinkList 'a' ('b' :: [])
testLinkList = refl

{-
testLL[] : (ll[] 'a' ('b' :: [])) ≡ LinkList 'a' ('b' :: [])
testLL[] = ?
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

{-

t0 : Trie []
t0 = node ff []

t1 : Trie []
t1 = node tt []

t2 : Trie []
t2 = node ff (link 'a' (node tt []) :: [])

t3 : Trie []
t3 = node ff
 (link 'a' (node tt []) ::
 (link 'o' (node ff (link 'n' (node tt []) :: []))) ::
 [])

{- to compute all of the words in `t` -}
wordst : ∀ l -> (t : Trie l) -> 𝕃 (𝕃 char)

{- to compute all of the words in `lst`, which are the children of some Trie -}
wordsl : ∀ l -> (lst : 𝕃 (Link l)) -> 𝕃 (𝕃 char)


wordst l (node tt children) = l :: wordsl l children
wordst l (node ff children) = wordsl l children
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

-}
