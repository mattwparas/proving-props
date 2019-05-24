{- 

Proving the correctness of sorting using a trie data structure

Alexandra Grimes and Matthew Paras

Date : 5/24/19

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



{- compare two character lists for equality -}

_list-char=_ : 𝕃 char → 𝕃 char → 𝔹
_list-char=_ [] [] = tt
_list-char=_ (x :: l1) [] = ff
_list-char=_ [] (y :: l2) = ff
_list-char=_ (x :: l1) (y :: l2) = _list-char=_ l1 l2



{-
An internal node of a trie is defined by the characters that precede it

Contains a list of children defined by the next character added onto it

-}
data INTERN-TRIE {ℓ}(A : Set ℓ) : 𝕃 char →  Set where
   Node : ∀ { lst : 𝕃 char } →
        (character : char)
        → (end? : 𝔹)
        → (children : 𝕃 (INTERN-TRIE A (lst ++ character :: [])))
      {-  → (children-are-in-order : tt) -}
        → (prefix : 𝕃 char)
        → {prefix-same-proof : prefix list-char= (lst ++ character :: []) ≡ tt}
        → INTERN-TRIE A lst



{- children of the root node will always be defined by empty prefix -}
data ROOT-TRIE {ℓ}(A : Set ℓ) : Set where
  Node : (children : 𝕃 (INTERN-TRIE A [])) → ROOT-TRIE A



empty-root-trie : ∀{ℓ}{A : Set ℓ} → ROOT-TRIE A
empty-root-trie = (Node [])



_intern-trie<list_ : ∀{ℓ}{A : Set ℓ}
                   → ∀ {lst : 𝕃 char}
                   → INTERN-TRIE A lst
                   → 𝕃 (INTERN-TRIE A lst)
                   → 𝔹

_intern-trie<list_ (Node character end? children prefix {prefix-same-proof}) [] = tt
_intern-trie<list_ (Node character end? children prefix {prefix-same-proof}) ((Node first-char first-end? first-children first-prefix {first-prefix-same-proof}) :: rest-list) with character <char first-char
... | tt = (Node character end? children prefix {prefix-same-proof}) intern-trie<list rest-list
... | ff = ff

intern-children-are-sorted :  ∀{ℓ}{A : Set ℓ} → ∀ {lst : 𝕃 char} → INTERN-TRIE A lst → 𝔹
intern-children-are-sorted (Node character end? [] prefix {proof}) = tt
intern-children-are-sorted (Node character end? (first-trie :: children) prefix {proof}) with first-trie intern-trie<list children
... | tt = intern-children-are-sorted (Node character end? children prefix {proof})
... | ff = ff


root-children-are-sorted :  ∀{ℓ}{A : Set ℓ} → ROOT-TRIE A → 𝔹
root-children-are-sorted (Node []) = tt
root-children-are-sorted (Node (first-trie :: children)) with first-trie intern-trie<list children
... | tt = root-children-are-sorted (Node children) -- double check this
... | ff = ff -- exit here


-- map problem here...
well-formed-trie :  ∀{ℓ}{A : Set ℓ} → ROOT-TRIE A → 𝔹
well-formed-trie (Node []) = ff
well-formed-trie (Node (x :: children)) = {!!}


-- Helper lemmas
list-one-element-length-equal-1 : ∀{ℓ}{A : Set ℓ} → (x : A) → (length (x :: [])) ≡ 1
list-one-element-length-equal-1 {ℓ} {A} x = refl

list-more-than-one-element-length>1 : ∀{ℓ}{A : Set ℓ} → (x y : A) → (l : 𝕃 A) → (length (x :: y :: l)) > 1 ≡ tt
list-more-than-one-element-length>1 {ℓ} {A} x y l = refl



create-children :  ∀{ℓ}{A : Set ℓ}
                → (lchars : 𝕃 char) -- word to insert
                → (prefix : 𝕃 char) -- prefix
                → 𝕃 (INTERN-TRIE A prefix) -- list of tries to push word into - this type also needs to be specified
                → is-empty lchars ≡ ff -- proof about the list of elements to insert
                → 𝕃 (INTERN-TRIE A prefix) -- return value... the type of this will need to change


handle-intern-letter :  ∀{ℓ}{A : Set ℓ}
                     → (lchars : 𝕃 char) -- word to insert
                     → (prefix : 𝕃 char) -- prefix
                     → 𝕃 (INTERN-TRIE A prefix) -- list of tries to push word into
                     → length (lchars) > 1 ≡ tt -- proof
                     → 𝕃 (INTERN-TRIE A prefix) -- result


handle-last-letter :  ∀{ℓ}{A : Set ℓ}
                   → (lchars : 𝕃 char) -- word to insert
                   → (prefix : 𝕃 char) -- prefix
                   → 𝕃 (INTERN-TRIE A prefix) -- list of tries to push word into
                   → length (lchars) ≡ 1 -- proof
                   → 𝕃 (INTERN-TRIE A prefix) -- result

-- create-children = {!!}

-- START DEFINITIONS OF HANDLE-INTERN-LETTER HERE
handle-intern-letter [] prefix list-tries ()
handle-intern-letter (x :: []) prefix list-tries ()
handle-intern-letter (x :: y :: lchars) prefix [] length-lchars>1≡tt = {!!}
handle-intern-letter (x :: y :: lchars) prefix ((Node first-char first-end first-children first-prefix {first-proof}):: list-tries) length-lchars>1≡tt with x <char first-char
... | tt = {!!}
... | ff with x =char first-char
... | tt = {!!}
... | ff = {!!}

{- old handle-intern-letter:

handle-intern-letter [] ltries prefix-chars ()
handle-intern-letter (x :: []) ltries prefix-chars ()
handle-intern-letter (x :: y :: lchars) [] prefix-chars lchars>1 = (Node x ff (create-children (y :: lchars) [] (prefix-chars ++ x :: []) refl) (prefix-chars ++ x :: [])) :: [] -- refl fits here, when children are empty
handle-intern-letter (x :: y :: lchars) ((Node first-char first-end first-children first-prefix) :: ltries) prefix-chars lchars>1 with x <char first-char
... | tt = (Node x ff (create-children (y :: lchars) [] (prefix-chars ++ x :: []) refl ) (prefix-chars ++ x :: []))  :: (Node first-char first-end first-children first-prefix) :: ltries -- character is less than
... | ff with x =char first-char
... | tt = (Node x first-end (create-children (y :: lchars) first-children (prefix-chars ++ x :: []) refl) first-prefix) :: ltries  -- characters are the same
... | ff = (Node first-char first-end first-children first-prefix) :: (create-children (x :: y :: lchars) ltries prefix-chars refl) -- else case

-}



-- START DEFINITIONS OF HANDLE-LAST-LETTER HERE
handle-last-letter [] prefix list-tries ()
handle-last-letter (x :: []) prefix [] length-lchars=1≡tt = {!!} -- empty lst case
handle-last-letter (x :: []) prefix ((Node first-char first-end first-children first-prefix {first-proof}) :: list-tries) length-lchars=1≡tt with x <char first-char
... | tt = {!!}
... | ff with x =char first-char
... | tt = {!!}
... | ff = {!!}
handle-last-letter (x :: y :: lchars) prefix list-tries ()

{- old handle-last-letter:

handle-last-letter [] ltries prefix-chars ()
handle-last-letter (x :: []) [] prefix-chars len-lchars-eq-1 = (Node x tt [] (prefix-chars ++ x :: [])) :: []
handle-last-letter (x :: []) ((Node first-char first-end first-children first-prefix) :: ltries) prefix-chars len-lchars-eq-1 with x <char first-char
... | tt = (Node x tt [] (prefix-chars ++ x :: [])) :: (Node first-char first-end first-children first-prefix) :: ltries -- when the characters are < 
... | ff with x =char first-char
... | tt = (Node x tt first-children (prefix-chars ++ x :: [])) :: ltries -- please check this (when the characters are equal)
... | ff = (Node first-char first-end first-children first-prefix) :: (create-children (x :: []) ltries prefix-chars refl) -- this should be the else case -- see how the hole is actually refl
handle-last-letter (x :: y :: lchars) ltries prefix-chars ()

-}




-- START DEFINITIONS FOR CREATE CHILDREN HERE
create-children [] up-to-prefix list-tries ()
create-children (x :: []) up-to-prefix list-tries list-chars-not-empty = handle-last-letter (x :: []) up-to-prefix list-tries (list-one-element-length-equal-1 x)
create-children (x :: y :: word) up-to-prefix list-tries list-chars-not-empty = handle-intern-letter (x :: y :: word) up-to-prefix list-tries (list-more-than-one-element-length>1 x y word)


-- takes in the root trie, a list of input characters, a proof stating that the list of input characters is not empty, and returns a new root-trie
insert-string-into-trie :  ∀{ℓ}{A : Set ℓ}
                        → ROOT-TRIE A
                        → (lchars : 𝕃 char)
                        → is-empty lchars ≡ ff -- the 'contract' saying that the inserted word is not empty
                        → ROOT-TRIE A
insert-string-into-trie (Node root-children) list-chars not-empty-chars = Node (create-children list-chars [] root-children not-empty-chars)




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


pre-order-helper : ∀{ℓ}{A : Set ℓ} → ∀ {lst : 𝕃 char} → INTERN-TRIE A lst → 𝕃 (𝕃 char)
pre-order-helper = {!!}


pre-order : ∀{ℓ}{A : Set ℓ} → ROOT-TRIE A → 𝕃 (𝕃 char)
pre-order = {!!}


{-

OLD definitions
"Inline foldr and map" so that agda knows how the termination works


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

-}

-- see if a traversal is sorted
traversal-is-sorted : ∀{ℓ}{A : Set ℓ} → (all-roots : ROOT-TRIE A) → list-is-sorted(pre-order all-roots) ≡ tt
traversal-is-sorted = {!!}



-- prefix at node is the same as the path to that node
-- prefix-stub-here .............


{-
permutation stuff

lengths are equal

every member of l1 is in l2

every member of l2 is in l1

uniqueness...
-}


is-permutation : 𝕃 (𝕃 char) → 𝕃 (𝕃 char) → 𝔹
is-permutation = {!!}


-- Here is the sorting function, right now it does nothing
trie-sort : 𝕃 string → 𝕃 string
trie-sort lst = {!!}


