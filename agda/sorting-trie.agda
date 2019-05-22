{- 

Proving the correctness of sorting using a trie ~in agda~

Starring:

Alexandra Grimes

      and

 Matthew Paras

Stay tuned!!!!!

-}
open import bool
open import char
open import list
open import maybe
open import product
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

{-
data trie (A : Set) : Set where
  Node : maybe A → cal (trie A) → trie A
-}

{-
cal seems to represent a hash map? Could represent some other stuff thought not sure
-}
cal : Set → Set
cal A = 𝕃 (char × A)

empty-cal : ∀{A : Set} → cal A
empty-cal = []

cal-lookup : ∀ {A : Set} → cal A → char → maybe A
cal-lookup [] _ = nothing
cal-lookup ((c , a) :: l) c' with c =char c'
... | tt = just a
... | ff = cal-lookup l c'


{-
Need to change the comparator function, change this so its not explicitly a hashmap but rather a list of children
Otherwise we can work with this I think...
-}
cal-insert : ∀ {A : Set} → cal A → char → A → cal A
cal-insert [] c a = (c , a) :: []
cal-insert ((c' , a') :: l) c a with c =char c'
... | tt = (c , a) :: l
... | ff = (c' , a') :: (cal-insert l c a)

cal-remove : ∀ {A : Set} → cal A → char → cal A
cal-remove [] _ = []
cal-remove ((c , a) :: l) c' with c =char c'
... | tt = cal-remove l c'
... | ff = (c , a) :: cal-remove l c'

cal-add : ∀{A : Set} → cal A → char → A → cal A
cal-add l c a = (c , a) :: l







{-
trie-sort : ∀ {A : Set} -> 𝕃char -> 𝕃char
trie-sort = ?
-}

{-
data trie (A : Set) : Set where
  Node : maybe A → 𝔹 → cal (trie A) → 𝕃 char → trie A
-}



data TRIE : Set where
  Node :
      (character : maybe char)
    → (end? : 𝔹)
    → (children : 𝕃 (TRIE))
    → (prefix : 𝕃 char)
      → TRIE


empty-trie : TRIE
empty-trie = (Node nothing ff [] [])

build-trie : char -> TRIE
build-trie a = (Node (just a) ff [] [])


-- children-lookup : 𝕃(TRIE) → char → 


-- "Is this character in my children?"
lookup-char-children : TRIE -> char -> 𝔹
lookup-char-children (Node character end? [] prefix) c = ff
lookup-char-children (Node character end? ((Node (just x) child-end? child-children child-prefix) :: children) prefix) c with c =char x
... | tt = tt
... | ff = lookup-char-children (Node character end? children prefix) c
lookup-char-children (Node character end? ((Node nothing child-end? child-children child-prefix) :: children) prefix) c = ff {- BOGUS CASE -}


-- "Is this list of characters (string) in the trie?"
lookup-string : TRIE -> 𝕃 char -> 𝔹
lookup-string (Node character end? children prefix) [] = ff -- empty string case
lookup-string (Node (just c) end? children prefix) (x :: listofchars) with c =char x
lookup-string (Node (just c) end? children prefix) (x :: []) | tt = end? -- if we're at the last character in our input, return 'end?'
lookup-string (Node (just c) end? children prefix) (x :: y :: listofchars) | tt = {!!} -- this is where we need to call map?
... | ff = ff
lookup-string (Node nothing end? children prefix) (x :: listofchars) = ff {- BOGUS CASE -}



trie-insert : TRIE -> 𝕃 char → TRIE
trie-insert = {!!}









{-

cal-lookup : ∀ {A : Set} → cal A → char → maybe A
cal-lookup [] _ = nothing
cal-lookup ((c , a) :: l) c' with c =char c'
... | tt = just a
... | ff = cal-lookup l c'

-}


{-
data trie1 : char → 𝔹 → cal (trie1) → 𝕃 char → Set where
  Node : {c : char} → {b : 𝔹} → {A : cal(TRIE)} → {x : 𝕃 char} → trie1 c b A x 
-}

-- random-proof : TRIE → 


-- Here is the sorting function, right now it does nothing
trie-sort : 𝕃 string → 𝕃 string
trie-sort lst = lst



data BST : ℕ -> ℕ -> Set where
  leaf : ∀ {n m} -> {n≤m : n ≤ m ≡ tt} -> BST n m
  node : ∀ {l' l u' u}
      -> (n : ℕ) -> (left : BST l' n) -> (right : BST n u')
      -> {l≤l' : l ≤ l' ≡ tt} -> {u'≤u : u' ≤ u ≡ tt}
      -> BST l u


{-

data TRIE : (A : char) → Set where
  Node : maybe A → 𝔹 → cal (trie A) → 𝕃 char → trie A

-}

