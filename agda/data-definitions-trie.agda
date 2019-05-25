{- 

Proving the correctness of sorting using a trie data structure in ~agda~

Starring:

  Alexandra Grimes 
      
        and 
    
   Matthew Paras

Date : 5/24/19

-}

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



{- Function to test if two "words" are equal
 - a "word" is represented by a list of chars
-} 
_list-char=_ : 𝕃 char → 𝕃 char → 𝔹
_list-char=_ [] [] = tt
_list-char=_ (x :: l1) [] = ff
_list-char=_ [] (y :: l2) = ff
_list-char=_ (x :: l1) (y :: l2) with x =char y
... | tt = _list-char=_ l1 l2
... | ff = ff



{- An internal node of a trie is defined by the characters that precede it
 - Each trie contains a list of children defined by appending the char in that child to the parent's prefix

- Each Node has:
  - character
  - end?
  - children of tries
  - prefix and proof that this prefix is defined correctly
           { Note: we think this will help to prove the traversal in order }
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



{- The root trie is different because it doesn't need the prefix, character, or end?

 - Each Node has:
  - list of children tries (INTERN_TRIES) 
  - children of the root node will always be defined by empty prefix 
-}
data ROOT-TRIE {ℓ}(A : Set ℓ) : Set where
  Node : (children : 𝕃 (INTERN-TRIE A [])) → ROOT-TRIE A



{- A base structure to start inserting words
 - However, you could add words to an existing ROOT-TRIE as well 
-}
empty-root-trie : ∀{ℓ}{A : Set ℓ} → ROOT-TRIE A
empty-root-trie = (Node [])



{- Function that returns a boolean for whether the char of an INTERN_TRIE is less than all chars in in the list of INTERN_TRIEs 
 - Less than for a character is defined position in the alphabet
-}
_intern-trie<list_ : ∀{ℓ}{A : Set ℓ}
                   → ∀ {lst : 𝕃 char}
                   → INTERN-TRIE A lst
                   → 𝕃 (INTERN-TRIE A lst)
                   → 𝔹
_intern-trie<list_ (Node character end? children prefix {prefix-same-proof})
                   [] = tt
_intern-trie<list_ (Node character end? children prefix {prefix-same-proof})
                   ((Node first-char first-end? first-children first-prefix {first-prefix-same-proof}) :: rest-list) with character <char first-char
... | tt = (Node character end? children prefix {prefix-same-proof}) intern-trie<list rest-list
... | ff = ff



{- Function that takes an INTERN_TREE and returns a boolean about whether the node's children are sorted
 - Sort means the chars of the children tries are in alphabetical order 
-}
intern-children-are-sorted :  ∀{ℓ}{A : Set ℓ}
                           → ∀ {lst : 𝕃 char}
                           → INTERN-TRIE A lst
                           → 𝔹
intern-children-are-sorted (Node character end? [] prefix {proof}) = tt
intern-children-are-sorted (Node character end? (first-trie :: children) prefix {proof}) with first-trie intern-trie<list children
... | tt = intern-children-are-sorted (Node character end? children prefix {proof})
... | ff = ff



{-Same as the function above but handles the case for the root trie 
- Does not need the quantifier over all lst because ROOT-TRIE does not take a list
-} 
root-children-are-sorted :  ∀{ℓ}{A : Set ℓ} → ROOT-TRIE A → 𝔹
root-children-are-sorted (Node []) = tt
root-children-are-sorted (Node (first-trie :: children)) with first-trie intern-trie<list children
... | tt = root-children-are-sorted (Node children) -- double check this
... | ff = ff -- exit here



{-Function that returns a boolean about whether the trie is "well-formed"
- Well formed means that all the children are in order for all nodes
              { Note 1: We are doing external verification about the order of the children, 
                            but internal verification that the prefixes are well-formed??}
              { Note 2: Issue with using map here, like we did in Racket but will have to 
                        do that more manually in the future}
 -}
well-formed-trie :  ∀{ℓ}{A : Set ℓ} → ROOT-TRIE A → 𝔹
well-formed-trie (Node []) = ff
well-formed-trie (Node (x :: children)) = {!!}



{- Helper lemma -}
list-one-element-length-equal-1 : ∀{ℓ}{A : Set ℓ} → (x : A) → (length (x :: [])) ≡ 1
list-one-element-length-equal-1 {ℓ} {A} x = refl



{- Helper Lemma -}
list-more-than-one-element-length>1 : ∀{ℓ}{A : Set ℓ} → (x y : A) → (l : 𝕃 A) → (length (x :: y :: l)) > 1 ≡ tt
list-more-than-one-element-length>1 {ℓ} {A} x y l = refl



{- Helper for inserting words into the trie, as you have to rebuild the children at each step -}
create-children :  ∀{ℓ}{A : Set ℓ}
                → (lchars : 𝕃 char) -- word to insert
                → (prefix : 𝕃 char) -- prefix
                → 𝕃 (INTERN-TRIE A prefix) -- list of tries to push word into
                → is-empty lchars ≡ ff -- proof about the list of elements to insert
                → 𝕃 (INTERN-TRIE A prefix) -- return value

{- Helper for handling when you are inserting a character that is NOT the last character in the list -}
handle-intern-letter :  ∀{ℓ}{A : Set ℓ}
                     → (lchars : 𝕃 char) -- word to insert
                     → (prefix : 𝕃 char) -- prefix
                     → 𝕃 (INTERN-TRIE A prefix) -- list of tries to push word into
                     → length (lchars) > 1 ≡ tt -- proof
                     → 𝕃 (INTERN-TRIE A prefix) -- result

{- Helper for handling when you are inserting a character that IS the last character in the list -}
handle-last-letter :  ∀{ℓ}{A : Set ℓ}
                   → (lchars : 𝕃 char) -- word to insert
                   → (prefix : 𝕃 char) -- prefix
                   → 𝕃 (INTERN-TRIE A prefix) -- list of tries to push word into
                   → length (lchars) ≡ 1 -- proof
                   → 𝕃 (INTERN-TRIE A prefix) -- result

-- START DEFINITIONS OF HANDLE-INTER-LETTER HERE
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
create-children (x :: [])
                up-to-prefix
                list-tries
                list-chars-not-empty = (handle-last-letter (x :: [])
                                                           up-to-prefix
                                                           list-tries
                                                           (list-one-element-length-equal-1 x))
create-children (x :: y :: word)
                up-to-prefix
                list-tries
                list-chars-not-empty = (handle-intern-letter (x :: y :: word)
                                                             up-to-prefix list-tries
                                                             (list-more-than-one-element-length>1 x y word))

{- old create-children:

create-children [] up-to-prefix list-tries ()
create-children (x :: word) up-to-prefix list-tries list-chars-not-empty with keep (length word =ℕ 0)
... | tt , len≡0 = {!handle-last-letter (x :: []) up-to-prefix list-tries len≡0!}
... | ff , len!≡0 = {!!} 
-}



{- Creates a new trie with a single new word inserted into it
- Arguments:
  - root trie
  - list of chars (to represent the new word)
  - a proof that the input characters is not empty
                 { Note: this assumption is what makes our Racket code work}
-}
insert-string-into-trie :  ∀{ℓ}{A : Set ℓ}
                        → ROOT-TRIE A
                        → (lchars : 𝕃 char)
                        → is-empty lchars ≡ ff -- the 'contract' saying that the inserted word is not empty
                        → ROOT-TRIE A
insert-string-into-trie (Node root-children)
                        list-chars not-empty-chars = Node (create-children list-chars [] root-children not-empty-chars)



{- Function that returns a boolean about whether all "words" in a list of "words" are all not empty -}
all-words-not-empty : 𝕃 (𝕃 char) → 𝔹
all-words-not-empty [] = tt -- come back to this
all-words-not-empty ([] :: rest-words) = ff
all-words-not-empty ((first-char :: rest-chars) :: rest-words) = all-words-not-empty rest-words



{- Note: need a lemma that states that all-words-not-empty -> first word not empty -}



{- Builds a trie from a list of strings
- Has proofs as arguments that were the assumptions that we used in our Racket code about empty words
-} 
insert-lstrings-into-trie : ∀{ℓ}{A : Set ℓ} → ROOT-TRIE A → (lst : 𝕃 (𝕃 char)) → is-empty lst ≡ ff → all-words-not-empty lst ≡ tt → ROOT-TRIE A
insert-lstrings-into-trie rooted-trie [] ()
insert-lstrings-into-trie rooted-trie (first-word :: []) lst-not-empty words-not-empty = insert-string-into-trie rooted-trie first-word {!!}
insert-lstrings-into-trie rooted-trie (first-word :: second-word :: rest-word-list) lst-not-empty words-not-empty
  = insert-lstrings-into-trie (insert-string-into-trie rooted-trie first-word {!!}) (second-word :: rest-word-list) refl {!!}



{- Function that returns a boolean about whether a string is less than another string,
- Helper for list-is-sorted
-}
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



{- Function that returns a boolean about whether a string is less than all the other string in a list
- Helper for list-is-sorted
-}
-- given string, see if it is less than all other strings in the list
_string<list_ : 𝕃 char → 𝕃 (𝕃 char) → 𝔹
_string<list_ comp-string [] = tt
_string<list_ comp-string (first-string :: rest-strings) with comp-string string< first-string
... | tt = comp-string string<list rest-strings
... | ff = ff



{- given list of strings, see if the list of strings is in the right order
              { Note: Useful for external verification? }
-}
list-is-sorted : 𝕃 (𝕃 char) → 𝔹
list-is-sorted [] = tt
list-is-sorted (first-string :: rest-of-words) with first-string string<list rest-of-words
... | tt = list-is-sorted rest-of-words
... | ff = ff



{- Takes an INTERN-TRIE and returns a list of "strings" that is created by traversing the trie in pre-order 
- Helper for pre-order
-}
pre-order-helper : ∀{ℓ}{A : Set ℓ} → ∀ {lst : 𝕃 char} → INTERN-TRIE A lst → 𝕃 (𝕃 char)
pre-order-helper = {!!}



{- Takes a ROOT-TRIE and returns a list of "strings" that is created by traversing the trie in pre-order 
- Should create the sorted list!
-}
pre-order : ∀{ℓ}{A : Set ℓ} → ROOT-TRIE A → 𝕃 (𝕃 char)
pre-order (Node []) = []
pre-order (Node (x :: children)) = {!!}


{- old definitions:

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

{- WE WILL NEED THIS THEOREM: prefix at node is the same as the path to that node -}

-- THEOREMS ABOUT THE INPUT AND INPUT/OUTPUT RELATION


{-
permutation stuff

lengths are equal

every member of l1 is in l2

every member of l2 is in l1

uniqueness...
-}

-- just like member in Racket
is-member : 𝕃 char → 𝕃 (𝕃 char) → 𝔹
is-member character [] = ff
is-member character (x :: lst) with character list-char= x
... | tt = tt
... | ff = is-member character lst

-- every element in list1 is also in list2?
every-element-in-list : 𝕃 (𝕃 char) → 𝕃 (𝕃 char) → 𝔹
every-element-in-list [] l2 = tt
every-element-in-list (x :: l1) l2 with is-member x l2
... | tt = every-element-in-list l1 l2
... | ff = ff

-- deterines whether two lists are permutations of each other
-- Note: Perhaps a proof about the uniqueness of words that go into the trie?
is-permutation : 𝕃 (𝕃 char) → 𝕃 (𝕃 char) → 𝔹
is-permutation l1 l2 = (length l1 =ℕ length l2) && (every-element-in-list l1 l2) && (every-element-in-list l2 l1)

-- see if a traversal is sorted
traversal-is-sorted : ∀{ℓ}{A : Set ℓ} → (all-roots : ROOT-TRIE A) → list-is-sorted(pre-order all-roots) ≡ tt
traversal-is-sorted (Node []) = refl
traversal-is-sorted (Node (first :: children)) = {!!}

-- traversal-is-a-permutation : ∀{ℓ}{A : Set ℓ} → (all-roots : ROOT-TRIE A)
-- traversal-is-a-permutation : ∀{ℓ}{A : Set ℓ} → (all-roots : ROOT-TRIE A) → is-permutation(pre-order all-roots)
-- traversal-is-a-permutation = {!!}

-- input l1
-- build trie from l1
-- l2 = get words out of trie
-- compare l1 and l2
-- type at node is same as path to get there

-- Here is the sorting function, right now it does nothing
trie-sort : 𝕃 string → 𝕃 string
trie-sort lst = {!!}


