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


data Trie : 𝕃 char -> Set
data Link : 𝕃 char -> Set

data Trie where
  node : ∀ {l : 𝕃 char} -> (wordp : bool) -> (children : 𝕃 (Link l)) -> Trie l

data Link where
  link : ∀ (c : char) { l : 𝕃 char } -> (child : Trie (l ++ ( c :: []))) -> Link l

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


