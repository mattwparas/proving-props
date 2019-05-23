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

--open import negation



data INTERN-TRIE {ℓ}(A : Set ℓ) : Set where
  Node :
      (character : char)
    → (end? : 𝔹)
    → (children : 𝕃 (INTERN-TRIE A))
    → (prefix : 𝕃 char)
      → INTERN-TRIE A


data ROOT-TRIE {ℓ}(A : Set ℓ): Set where
  Node : (children : 𝕃 (INTERN-TRIE A))
      → ROOT-TRIE A




-- an empty trie
empty-root-trie : ∀{ℓ}{A : Set ℓ} → ROOT-TRIE A
empty-root-trie = (Node [])


_intern-trie<list_ : ∀{ℓ}{A : Set ℓ} → INTERN-TRIE A → 𝕃 (INTERN-TRIE A) → 𝔹
_intern-trie<list_ (Node character end? children prefix) [] = tt -- is this valid?
_intern-trie<list_ (Node character end? children prefix) ((Node first-char first-end? first-children first-prefix) :: rest-list) with character <char first-char
... | tt = (Node character end? children prefix) intern-trie<list rest-list
... | ff = ff


intern-children-are-sorted : ∀{ℓ}{A : Set ℓ} → INTERN-TRIE A → 𝔹
intern-children-are-sorted (Node character end? [] prefix) = tt -- children are empty, default is sorted
intern-children-are-sorted (Node character end? (first-trie :: children) prefix) with first-trie intern-trie<list children
... | tt = intern-children-are-sorted (Node character end? children prefix) -- recur here 
... | ff = ff -- exit here

root-children-are-sorted :  ∀{ℓ}{A : Set ℓ} → ROOT-TRIE A → 𝔹
root-children-are-sorted (Node []) = tt
root-children-are-sorted (Node (first-trie :: children)) with first-trie intern-trie<list children
... | tt = root-children-are-sorted (Node children) -- double check this
... | ff = ff -- exit here




list-one-element-length-equal-1 : ∀{ℓ}{A : Set ℓ} → (x : A) → (length (x :: [])) ≡ 1
list-one-element-length-equal-1 {ℓ} {A} x = refl

list-more-than-one-element-length>1 : ∀{ℓ}{A : Set ℓ} → (x y : A) → (l : 𝕃 A) → (length (x :: y :: l)) > 1 ≡ tt
list-more-than-one-element-length>1 {ℓ} {A} x y l = refl


-- maybe need to pass along the proof that list of characters has one element
create-children :  ∀{ℓ}{A : Set ℓ} → (lchars : 𝕃 char) → 𝕃 (INTERN-TRIE A) → 𝕃 char → is-empty lchars ≡ ff → 𝕃 (INTERN-TRIE A)


handle-intern-letter :  ∀{ℓ}{A : Set ℓ} → (lchars : 𝕃 char) → 𝕃 (INTERN-TRIE A) → 𝕃 char → length lchars > 1 ≡ tt → 𝕃 (INTERN-TRIE A)


handle-last-letter :  ∀{ℓ}{A : Set ℓ} → (lchars : 𝕃 char) → 𝕃 (INTERN-TRIE A) → 𝕃 char → length lchars ≡ 1 → 𝕃 (INTERN-TRIE A)


--handle-last-letter : (lchars : 𝕃 char) → 𝕃 INTERN-TRIE → 𝕃 char → is-empty lchars ≡ ff → 𝕃 INTERN-TRIE
-- START DEFITIONS FOR HANDLE LAST LETTER HERE
handle-last-letter [] ltries prefix-chars ()
handle-last-letter (x :: []) [] prefix-chars len-lchars-eq-1 = (Node x tt [] (prefix-chars ++ x :: [])) :: []
handle-last-letter (x :: []) ((Node first-char first-end first-children first-prefix) :: ltries) prefix-chars len-lchars-eq-1 with x <char first-char
... | tt = (Node x tt [] (prefix-chars ++ x :: [])) :: (Node first-char first-end first-children first-prefix) :: ltries -- when the characters are < 
... | ff with x =char first-char
... | tt = (Node x tt first-children (prefix-chars ++ x :: [])) :: ltries -- please check this (when the characters are equal)
... | ff = (Node first-char first-end first-children first-prefix) :: (create-children (x :: []) ltries prefix-chars refl) -- this should be the else case -- see how the hole is actually refl
handle-last-letter (x :: y :: lchars) ltries prefix-chars ()

-- maybe need to pass along the proof that the list of characters > one element
-- handle-intern-letter : (lchars : 𝕃 char) → 𝕃 INTERN-TRIE → 𝕃 char → is-empty lchars ≡ ff → 𝕃 INTERN-TRIE

-- START DEFINITIONS FOR HANDLING INTERNAL LETTERS HERE
handle-intern-letter [] ltries prefix-chars ()
handle-intern-letter (x :: []) ltries prefix-chars ()
handle-intern-letter (x :: y :: lchars) [] prefix-chars lchars>1 = (Node x ff (create-children (y :: lchars) [] (prefix-chars ++ x :: []) refl) (prefix-chars ++ x :: [])) :: [] -- refl fits here, when children are empty
handle-intern-letter (x :: y :: lchars) ((Node first-char first-end first-children first-prefix) :: ltries) prefix-chars lchars>1 with x <char first-char
... | tt = (Node x ff (create-children (y :: lchars) [] (prefix-chars ++ x :: []) refl ) (prefix-chars ++ x :: []))  :: (Node first-char first-end first-children first-prefix) :: ltries -- character is less than
... | ff with x =char first-char
... | tt = (Node x first-end (create-children (y :: lchars) first-children (prefix-chars ++ x :: []) refl) first-prefix) :: ltries  -- characters are the same
... | ff = (Node first-char first-end first-children first-prefix) :: (create-children (x :: y :: lchars) ltries prefix-chars refl) -- else case

-- requires giving the proof that the input list of variables is not empty
-- create-children : (lchars : 𝕃 char) → 𝕃 INTERN-TRIE → 𝕃 char → is-empty lchars ≡ ff → 𝕃 INTERN-TRIE

-- START DEFINITIONS FOR CREATE CHILDREN HERE
create-children [] list-tries up-to-prefix ()
create-children (x :: []) list-tries up-to-prefix list-chars-not-empty = handle-last-letter (x :: []) list-tries up-to-prefix (list-one-element-length-equal-1 x)
create-children (x :: y :: list-chars) list-tries up-to-prefix list-chars-not-empty = handle-intern-letter (x :: y :: list-chars) list-tries up-to-prefix (list-more-than-one-element-length>1 x y list-chars)


-- takes in the root trie, a list of input characters, a proof stating that the list of input characters is not empty, and returns a new root-trie
insert-string-into-trie :  ∀{ℓ}{A : Set ℓ} → ROOT-TRIE A → (lchars : 𝕃 char) → is-empty lchars ≡ ff → ROOT-TRIE A
insert-string-into-trie (Node root-children) list-chars not-empty-chars = Node (create-children list-chars root-children [] not-empty-chars)




{- SORTED LIST DEFINITIONS AND THINGS OF THE SORT -}


-- compare the order of 2 strings (which are just list of chars)
-- TODO check up on the function definitions here
_string<_ : 𝕃 char → 𝕃 char → 𝔹
_string<_ [] [] = tt
_string<_ [] (x :: string2) = tt -- "" < "a : pple"
_string<_ (x :: string1) [] = ff -- "a : pple" < ""
_string<_ (x :: string1) (y :: string2) with x <char y
... | tt = tt -- "a : (pple)" < "b : (eets)"
... | ff with x =char y
... | tt =  string1 string< string2 -- if they are equal, recur on the next char "a : (pple)" = "a : (ble)" -> "p : (ple)" < "b : (le)"
... | ff = ff -- else case


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



{- this shits whack, needs to probably change, maybe don't use map?????? 

inclination is that the depth of the tree is bounded by the length of the longest word

IDEA:
Store length of the longest word in the root node, pass current depth or some shit idk that 
way agda knows the depth is decreasing and the calls will eventually stop...

-}
pre-order-helper :  ∀{ℓ}{A : Set ℓ} → INTERN-TRIE A → 𝕃 (𝕃 char)
pre-order-helper (Node character end? [] prefix) = []
pre-order-helper (Node character end? ((Node first-char first-end first-children first-prefix) :: children) prefix) with first-end
... | tt =  {!!} -- foldr _++_ (first-prefix :: []) (map pre-order-helper first-children)
... | ff = {!!} -- foldr _++_ [] (map pre-order-helper first-children)

pre-order :  ∀{ℓ}{A : Set ℓ} → ROOT-TRIE A → 𝕃 (𝕃 char)
pre-order (Node []) = []
pre-order (Node ((Node first-char first-end first-children first-prefix) :: children)) with first-end
... | tt = {!!}
... | ff = {!!}

-- (foldr _++_ (first-prefix :: []) (map pre-order-helper first-children))


-- see if a traversal is sorted
traversal-is-sorted : ∀{ℓ}{A : Set ℓ} → (all-roots : ROOT-TRIE A) → list-is-sorted(pre-order all-roots) ≡ tt
traversal-is-sorted = {!!}












is-permutation : 𝕃 (𝕃 char) → 𝕃 (𝕃 char) → 𝔹
is-permutation = {!!}


-- Here is the sorting function, right now it does nothing
trie-sort : 𝕃 string → 𝕃 string
trie-sort lst = {!!}


