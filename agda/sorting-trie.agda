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


-- Here is the sorting function, right now it does nothing
trie-sort : 𝕃 string → 𝕃 string
trie-sort lst = lst



