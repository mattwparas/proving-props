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

data INTERN-TRIE : Set where
  Node :
      (character : char)
    → (end? : 𝔹)
    → (children : 𝕃 (INTERN-TRIE))
    → (prefix : 𝕃 char)
      → INTERN-TRIE


data ROOT-TRIE : Set where
  Node : (children : 𝕃 (INTERN-TRIE))
      → ROOT-TRIE


{-
data TRIE : Set where
  Node :
      (character : maybe char)
    → (end? : 𝔹)
    → (children : 𝕃 (TRIE))
    → (prefix : 𝕃 char)
      → TRIE


data TRIE2 : Set where
  Root : (children : 𝕃 (TRIE)) → TRIE2
  Leaf :
       (character : maybe char)
     → (end? : 𝔹)
     → (children : 𝕃 (TRIE2))
     → (prefix : 𝕃 char)
       → TRIE2

-}

{-
empty-trie : TRIE
empty-trie = (Node nothing ff [] [])
-}


{-
build-trie : char -> TRIE
build-trie a = (Node (just a) ff [] [])
-}

-- children-lookup : 𝕃(TRIE) → char → 


{-
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
-}

{-
trie-insert : TRIE -> 𝕃 char → TRIE
trie-insert = {!!}
-}

-- "add a listof char to the trie, return the trie"




{-
-- "Given a TRIE, are all of the children in the correct order?"
-- Can check that children are in order via (children-are-in-order TRIE ≡ tt) - that is our implication that we need
children-are-in-order : TRIE → 𝔹
children-are-in-order (Node character end? [] prefix) = tt -- children list is empty -> return true
children-are-in-order (Node (just character) end? ((Node (just x) child-end? child-children child-prefix) :: children) prefix) with character <char x
... | tt = children-are-in-order (Node (just x) child-end? child-children child-prefix) -- character < first of children list, recur with rest
... | ff = ff -- character not less than
children-are-in-order (Node nothing end? ((Node (just x) child-end? child-children child-prefix) :: children) prefix) = ff -- BOGUS CASE
children-are-in-order (Node (just character) end? ((Node nothing child-end? child-children child-prefix) :: children) prefix) = tt -- BOGUS CASE
children-are-in-order (Node nothing end? ((Node nothing child-end? child-children child-prefix) :: children) prefix) = ff -- BOGUS CASE
-}


{-
-- "Given a list of TRIEs, check that the first child is less than all of the other children"
_trie<list_ : TRIE → 𝕃 TRIE → 𝔹
_trie<list_ (Node character end? children prefix) [] = tt
_trie<list_ (Node (just x) end? children prefix) ((Node (just first-char) first-end? first-children first-prefix) :: rest-children) with x <char first-char
... | tt = (Node (just x) end? children prefix) trie<list rest-children
... | ff = ff
_trie<list_ (Node (just x) end? children prefix) ((Node nothing first-end? first-children first-prefix) :: rest-children) = ff -- weird case here
_trie<list_ (Node nothing end? children prefix) ((Node first-char first-end? first-children first-prefix) :: rest-children) = ff -- weird case here


children-are-sorted : TRIE → 𝔹
children-are-sorted (Node character end? [] prefix) = tt -- children are empty, default is sorted
children-are-sorted (Node character end? (first-trie :: children) prefix) with first-trie trie<list children
... | tt = children-are-sorted (Node character end? children prefix)
... | ff = ff
-}



_intern-trie<list_ : INTERN-TRIE → 𝕃 INTERN-TRIE → 𝔹
_intern-trie<list_ (Node character end? children prefix) [] = tt -- is this valid?
_intern-trie<list_ (Node character end? children prefix) ((Node first-char first-end? first-children first-prefix) :: rest-list) with character <char first-char
... | tt = (Node character end? children prefix) intern-trie<list rest-list
... | ff = ff


intern-children-are-sorted : INTERN-TRIE → 𝔹
intern-children-are-sorted (Node character end? [] prefix) = tt -- children are empty, default is sorted
intern-children-are-sorted (Node character end? (first-trie :: children) prefix) with first-trie intern-trie<list children
... | tt = intern-children-are-sorted (Node character end? children prefix)
... | ff = ff -- exit here

root-children-are-sorted : ROOT-TRIE → 𝔹
root-children-are-sorted (Node []) = tt
root-children-are-sorted (Node (first-trie :: children)) with first-trie intern-trie<list children
... | tt = root-children-are-sorted (Node children) -- double check this
... | ff = ff -- exit here




-- if a trie is in a list, then the character will never be nothing



-- compare the order of 2 strings (which are just list of chars)
-- TODO check up on the function definitions here
_string<_ : 𝕃 char → 𝕃 char → 𝔹
_string<_ [] [] = tt
_string<_ [] (x :: string2) = tt -- "" < "a : pple"
_string<_ (x :: string1) [] = ff -- "a" < ""
_string<_ (x :: string1) (y :: string2) with x <char y
... | tt = tt -- "a : (pple)" < "b : (eets)"
... | ff with x =char y
... | tt =  string1 string< string2 -- if they are equal, recur on the next char "a : (pple)" = "a : (ble)" -> "p : (ple)" < "b : (le)"
... | ff = ff -- BOGUS case? should never happen I guess...


-- given string, see if it is less than all other strings in the list
_string<list_ : 𝕃 char → 𝕃 (𝕃 char) → 𝔹
_string<list_ comp-string [] = tt
_string<list_ comp-string (first-string :: rest-strings) with comp-string string< first-string
... | tt = comp-string string<list rest-strings
... | ff = ff

-- given list of strings, see if the list of strings is in the right order
list-is-sorted : 𝕃 (𝕃 char) → 𝔹
list-is-sorted [] = tt
list-is-sorted (first-string :: rest-of-words) with first-string string<list rest-of-words
... | tt = list-is-sorted rest-of-words
... | ff = ff


is-permutation : 𝕃 (𝕃 char) → 𝕃 (𝕃 char) → 𝔹
is-permutation = {!!}

{-

-- Result is sorted - get here later - maybe have to show the transitivity of string<
list-is-sorted : 𝕃 (𝕃 char) → 𝔹
list-is-sorted [] = tt -- if the list of strings is empty, it is sorted
list-is-sorted (first-string :: []) = tt -- if the list is just one string, its sorted
list-is-sorted (first-string :: second-string :: rest-of-list) with first-string string< second-string
... | tt = list-is-sorted (second-string :: rest-of-list) -- if the first-string < second-string, recur with next string as the front of the list
... | ff = ff

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

