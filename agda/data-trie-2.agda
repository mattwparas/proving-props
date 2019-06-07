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
open import bool-thms2
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
  primCharEquality : char → char → 𝔹
  primNatToChar    : ℕ → char

----------------------------------------------------------------------
-- character definitions
----------------------------------------------------------------------

{-

Define built in <= for characters

char to unicode value, compare numbers

-}
_<char2_ : char → char → 𝔹
_<char2_ c1 c2 = (primCharToNat c1) ≤ (primCharToNat c2)

_<char3_ : char → char → 𝔹
_<char3_ c1 c2 = (primCharToNat c1) < (primCharToNat c2)

{-

Define built in equality for characters

-}
_=char2_ : char → char → 𝔹
_=char2_ c1 c2 = (primCharToNat c1) =ℕ (primCharToNat c2)

{-

For a given list of characters (string) see if the list of characters are in order

-}
list-of-chars-sorted : 𝕃 char → 𝔹
list-of-chars-sorted [] = tt
list-of-chars-sorted (x :: []) = tt
list-of-chars-sorted (x :: y :: l) = (x <char3 y) && list-of-chars-sorted (y :: l)

char-refl : ∀ (c : char) → (c =char2 c) ≡ tt
char-refl c = =ℕ-refl (primCharToNat c)


{-
postulate
  2cast : ∀ (c : char) → primNatToChar (primCharToNat c) ≡ c


natChar= : ∀ (x y : ℕ) → x ≡ y → primNatToChar x ≡ primNatToChar y
natChar= x y p rewrite p = refl
-}


{-

char-same : ∀ (x y : char) → (x =char2 y) ≡ tt → x ≡ y
char-same x y p = {!!}

-}





-- nat-to-char x y (=ℕ-to-≡ {primCharToNat x} {primCharToNat y} p)

----------------------------------------------------------------------
-- string definitions
----------------------------------------------------------------------

{-

Function that returns true if the l1 <= l2

-}
_string≤_ : 𝕃 char → 𝕃 char → 𝔹
_string≤_ [] [] = tt
_string≤_ [] (x :: string2) = tt -- "" < "a : pple"
_string≤_ (x :: string1) [] = ff -- "a : pple" < ""
_string≤_ (x :: string1) (y :: string2) = (x <char3 y) || ((x =char2 y) && (string1 string≤ string2))

{- 

Function that returns a boolean about whether a string is less than all the other string in a list
Helper for list-is-sorted

-}
_string≤list_ : 𝕃 char → 𝕃 (𝕃 char) → 𝔹
_string≤list_ [] [] = tt
_string≤list_ [] (first-string :: rest-strings) = tt
_string≤list_ (x :: comp-string) [] = tt
_string≤list_ (x :: comp-string) (first-string :: rest-strings) = ((x :: comp-string) string≤ first-string) && ((x :: comp-string) string≤list rest-strings)

{- 

Given list of strings, see if the list of strings is in the right order

-}
list-is-sorted : 𝕃 (𝕃 char) → 𝔹
list-is-sorted [] = tt
list-is-sorted (first-string :: rest-of-words)  = (first-string string≤list rest-of-words) && (list-is-sorted rest-of-words)

{-

Given two lists of characters (string representations), 
return true if all the words in l1 are less than l2
{ Note: Does not say anything about sortedness of the lists }

-}

_listwords≤listwords_ : 𝕃 (𝕃 char) → 𝕃 (𝕃 char) → 𝔹
_listwords≤listwords_ [] l2 = tt
_listwords≤listwords_ (first :: rest) l2 = first string≤list l2 && (rest listwords≤listwords l2)

{- function that returns whether two words are string= -}
=string : 𝕃 char → 𝕃 char → 𝔹
=string [] [] = tt
=string [] (x :: l2) = ff
=string (x :: l1) [] = ff
=string (x1 :: l1) (x2 :: l2) = (x1 =char2 x2) && (=string l1 l2)

=string-refl : ∀ (l : 𝕃 char) → (=string l l) ≡ tt
=string-refl [] = refl
=string-refl (x :: l) rewrite char-refl (x) = (=string-refl l)


----------------------------------------------------------------------
-- Trie, Link, IsSorted definitions
----------------------------------------------------------------------

data Trie : 𝕃 char -> Set
data Link : 𝕃 char -> Set

--These two data definitions help to define our sorted list of links
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
_link<_ {l} (link c1 child1) (link c2 child2) = c1 <char3 c2


-- A proof that x is less than all values in xs
data _≤*_ {l} (x : Link l) where
  <[]  : x ≤* []
  _<::_ : ∀ {y ys} → (x link< y ≡ tt) → x ≤* ys → x ≤* (y :: ys)


-- Proof that a list is sorted
data IsSorted {l} where
  s[]  : IsSorted []
  _s::_ : ∀ {x xs} → x ≤* xs → IsSorted xs → IsSorted (x :: xs)


----------------------------------------------------------------------
-- Insert definitions
----------------------------------------------------------------------

insert : 𝕃 char → (t : Trie []) -> Trie []
insert [] t = t
insert (x :: []) t = {!!}
insert (x :: y :: l) t = {!!}


----------------------------------------------------------------------
-- Traversal definitions
----------------------------------------------------------------------

{- to compute all of the words in `t` -}
wordst : ∀ l -> (t : Trie l) -> 𝕃 (𝕃 char)

{- to compute all of the words in `lst`, which are the children of some Trie -}
wordsl : ∀ l -> (lst : 𝕃 (Link l)) -> IsSorted lst → 𝕃 (𝕃 char)

wordst l (node tt children proof) = l :: (wordsl l children proof)
wordst l (node ff children proof) = wordsl l children proof
wordsl l [] s[] = []
wordsl l (link c child :: lt) (x s:: proof) = (wordst (l ++ (c :: [])) child) ++ (wordsl l lt proof)


{- takes a list of links and returns a list of their associated characters -}
link-list-to-chars : ∀ {l : 𝕃 char} → Trie l → 𝕃 char
link-list-to-chars {l} (node wordp [] x) = []
link-list-to-chars {l} (node wordp (link c child :: children) (x s:: other)) = (c :: (link-list-to-chars {l} (node wordp children other)))

----------------------------------------------------------------------
-- Sorting definitions
----------------------------------------------------------------------

{- for all lists of words, appending empty word to the front is still sorted -}
cons-empty-sorting : ∀ (l : 𝕃 (𝕃 char)) → list-is-sorted ([] :: l) ≡ list-is-sorted l
cons-empty-sorting [] = refl
cons-empty-sorting (l :: lst) = refl

{- empty string is always less than or equal to all the others in the list -}
empty-string≤ : ∀ (lst : 𝕃 (𝕃 char)) → [] string≤list lst ≡ tt
empty-string≤ [] = refl
empty-string≤ (lst :: lst₁) = refl

{- for any two words and any two chars, if consing the chars to each list respectively leads to two equal strings, the characters are then equal -}
lemma-char : ∀ (l1 l2 : 𝕃 char) (c1 c2 : char) → =string (c1 :: l1) (c2 :: l2) ≡ tt → c1 =char2 c2 ≡ tt
lemma-char l1 l2 c1 c2 eqs = (&&-fst eqs)

{- if two strings are equal, they are also ≤ -}
string=-gives-≤ : ∀ (l1 l2 : 𝕃 char) → =string l1 l2 ≡ tt → l1 string≤ l2 ≡ tt
string=-gives-≤ [] [] l1=l2 = refl
string=-gives-≤ [] (x :: l2) ()
string=-gives-≤ (x :: l1) [] ()
string=-gives-≤ (x :: l1) (y :: l2) l1=l2 rewrite lemma-char l1 l2 x y l1=l2
                                                   | (string=-gives-≤ l1 l2 (&&-snd l1=l2))
                                                   | ||-tt ((primCharToNat x) < (primCharToNat y)) = refl

string-equality : ∀ (l : 𝕃 char) → l string≤ l ≡ tt
string-equality [] = refl
string-equality (x :: l) rewrite char-refl (x) | string-equality l | ||-tt ((primCharToNat x) < (primCharToNat x)) = refl

string≤firstword-list : ∀ (l1 l2 : 𝕃 char) (stringList : 𝕃 (𝕃 char)) → (l1 string≤ l2) && (l1 string≤list stringList) ≡ tt → l1 string≤list (l2 :: stringList) ≡ tt
string≤firstword-list [] [] [] proof = refl
string≤firstword-list [] [] (stringList :: stringList₁) proof = refl
string≤firstword-list [] (x :: l2) [] proof = refl
string≤firstword-list [] (x :: l2) (stringList :: stringList₁) proof = refl
string≤firstword-list (x :: l1) [] [] ()
string≤firstword-list (x :: l1) [] (stringList :: stringList₁) ()
string≤firstword-list (x :: l1) (x₁ :: l2) [] proof = proof
string≤firstword-list (x :: l1) (x₁ :: l2) (stringList :: stringList₁) proof = proof

-- string≤list

string≤list-comm : ∀ (l : 𝕃 char) (l1 l2 : 𝕃 (𝕃 char)) → l string≤list l1 ≡ tt → l string≤list l2 ≡ tt → l string≤list (l1 ++ l2) ≡ tt
string≤list-comm [] [] [] l<l1 l<l2 = refl
string≤list-comm (x :: l) [] [] l<l1 l<l2 = refl
string≤list-comm [] [] (lchars2 :: lchars3) l<l1 l<l2 = refl
string≤list-comm (x :: l) [] (lchars2 :: lchars3) l<l1 l<l2 = l<l2
string≤list-comm [] (lchars1 :: lchars2) [] l<l1 l<l2 = refl
string≤list-comm (x :: l) (lchars1 :: lchars2) [] l<l1 l<l2 rewrite ++[] lchars2 = l<l1
string≤list-comm [] (lchars1 :: lchars2) (lchars3 :: lchars4) l<l1 l<l2 = refl
string≤list-comm (x :: l) (firstString :: lchars2) (secondString :: lchars4) l<l1 l<l2 rewrite
  &&-fst {(x :: l) string≤ firstString} {(x :: l) string≤list lchars2} l<l1
  = string≤list-comm (x :: l) lchars2 (secondString :: lchars4) (&&-snd {(x :: l) string≤ firstString} {(x :: l) string≤list lchars2} l<l1)  (string≤firstword-list (x :: l) secondString lchars4 l<l2)


helper-string≤lemma : ∀ (l : 𝕃 char) (c : char) → =string l l ≡ tt → l string≤ (l ++ c :: []) ≡ tt
helper-string≤lemma [] c proof = refl
helper-string≤lemma (x :: l) c proof rewrite &&-fst { (x =char2 x) } { =string l l } proof | (helper-string≤lemma l c (=string-refl l)) | ||-tt (primCharToNat x < primCharToNat x) = refl

=char-trans : ∀ {c1 c2 c3 : char} → c1 =char2 c2 ≡ tt → c2 =char2 c3 ≡ tt → c1 =char2 c3 ≡ tt
=char-trans {c1} {c2} {c3} p1 p2 rewrite
  =ℕ-to-≡ {primCharToNat c1} {primCharToNat c2} p1
  | =ℕ-to-≡ {primCharToNat c2} {primCharToNat c3} p2 = =ℕ-refl (primCharToNat c3)



<char-trans : ∀ {c1 c2 c3 : char} → c1 <char3 c2 ≡ tt → c2 <char3 c3 ≡ tt → c1 <char3 c3 ≡ tt
<char-trans {c1} {c2} {c3} p1 p2 = <-trans {primCharToNat c1} {primCharToNat c2} {primCharToNat c3} p1 p2

<char=-trans : ∀ {c1 c2 c3 : char} → c1 <char3 c2 ≡ tt → c2 =char2 c3 ≡ tt → c1 <char3 c3 ≡ tt
<char=-trans {c1} {c2} {c3} p1 p2 rewrite char-refl c2 | =ℕ-to-≡ {primCharToNat c2} {primCharToNat c3} p2 = p1


<string-trans : ∀ (l1 l2 l3 : 𝕃 char) → l1 string≤ l2 ≡ tt → l2 string≤ l3 ≡ tt → l1 string≤ l3 ≡ tt
<string-trans [] [] [] l1<l2 l2<l3 = refl
<string-trans [] [] (x :: l3) l1<l2 l2<l3 = refl
<string-trans [] (x :: l2) [] l1<l2 l2<l3 = refl
<string-trans [] (x :: l2) (x₁ :: l3) l1<l2 l2<l3 = refl
<string-trans (x :: l1) [] [] ()
<string-trans (x :: l1) [] (x₁ :: l3) ()
<string-trans (x :: l1) (x₁ :: l2) [] l1<l2 ()
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 with (x =char2 z) && (l1 string≤ l3)
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | tt rewrite ||-tt (primCharToNat x < primCharToNat z) = refl
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff with keep (x <char3 y) | keep ((x =char2 y) && (l1 string≤ l2)) | keep (y <char3 z) | keep ((y =char2 z) && (l2 string≤ l3))
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | tt , p1 | tt , p2 | tt , p3 | _ , p4 rewrite <char-trans {x} {y} {z} p1 p3 = refl
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | tt , p1 | ff , p2 | tt , p3 | tt , p4 = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | tt , p1 | tt , p2 | ff , p3 | tt , p4 rewrite p1 | p2 | p3 | p4 | <char=-trans {x} {y} {z} p1 (&&-fst {primCharToNat y =ℕ primCharToNat z} {l2 string≤ l3} p4) = refl
-- <string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | tt , p1 | tt , p2 | tt , p3 | ff , p4 = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | tt , p1 | ff , p2 | ff , p3 | tt , p4 = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | tt , p1 | tt , p2 | ff , p3 | ff , p4 = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | tt , p1 | ff , p2 | tt , p3 | ff , p4 = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | tt , p1 | ff , p2 | ff , p3 | ff , p4 = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | ff , p1 | tt , p2 | tt , p3 | tt , p4 = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | ff , p1 | ff , p2 | tt , p3 | tt , p4 = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | ff , p1 | tt , p2 | ff , p3 | tt , p4 = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | ff , p1 | tt , p2 | tt , p3 | ff , p4 = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | ff , p1 | ff , p2 | ff , p3 | tt , p4 = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | ff , p1 | tt , p2 | ff , p3 | ff , p4 = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | ff , p1 | ff , p2 | tt , p3 | ff , p4 = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | ff , p1 | ff , p2 | ff , p3 | ff , p4 rewrite p1 | p2 | p3 | p4 = {!!}

{-

<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | tt , p1 | tt , p2 | tt , p3 | _ , p4 rewrite <char-trans {x} {y} {z} p1 p3 = refl
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | tt , p1 | tt , p2 | ff , p3 | tt , p4 rewrite p1 | p2 | p3 | p4 | <char=-trans {x} {y} {z} p1 (&&-fst {primCharToNat y =ℕ primCharToNat z} {l2 string≤ l3} p4) = refl
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | tt , p1 | tt , p2 | ff , p3 | ff , p4 rewrite p1 | p2 | p3 | p4 = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | tt , p1 | ff , p2 | tt , p3 | _ , p4 = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | ff , p1 | tt , p2 | = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | ff , p1 | ff , p2 | = {!!}

-}



{-
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 with (x <char3 y) | ((x =char2 y) && (l1 string≤ l2))
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | tt | tt = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | tt | ff = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | tt = {!!}
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 | ff | ff = {!!}
-}

{- with (x =char2 z) && (l1 string≤ l3)
... | tt rewrite ||-tt (primCharToNat x < primCharToNat z) = refl
... | ff with keep (x <char3 y) | keep (y <char3 z)
... | tt , x<y | tt , y<z rewrite <char-trans {x} {y} {z} x<y y<z = refl
... | tt , x<y | ff , y>z = {!!}
... | ff , x>y | tt , y<z = {!!}
... | ff , x>y | ff , y>z = {!!} -- bogus case????
-}




-- (<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3)


string≤string+c2 : ∀ (l1 : 𝕃 char) (c : char) → l1 string≤ (l1 ++ c :: []) ≡ tt
string≤string+c2 [] c = refl
string≤string+c2 (x :: l) c rewrite char-refl x | string≤string+c2 l c | (||-tt (primCharToNat x < primCharToNat x)) = refl 


string≤string+c : ∀ (l1 l2 : 𝕃 char) (c : char) → (l1 ++ c :: []) string≤ l2 ≡ tt → (l1 string≤ l2) ≡ tt
string≤string+c [] [] c proof = refl
string≤string+c [] (x :: l2) c proof = refl
string≤string+c (x :: l1) [] c ()
string≤string+c (x :: l1) (firstchar :: l2) c proof = <string-trans (x :: l1) (x :: l1 ++ c :: []) (firstchar :: l2) (string≤string+c2 (x :: l1) c) proof



string≤list+c : ∀ (l : 𝕃 char) (c : char) (lst : 𝕃 (𝕃 char)) → (l ++ c :: []) string≤list lst ≡ tt → l string≤list lst ≡ tt
string≤list+c [] c [] proof = refl
string≤list+c [] c (lst :: lst₁) proof = refl
string≤list+c (x :: l) c [] proof = refl
string≤list+c (x :: l) c (first :: rest) proof rewrite string≤string+c (x :: l) (first) c (&&-fst proof) = string≤list+c (x :: l) c rest (&&-snd proof)



helper-lemma : ∀ (l : 𝕃 char) (lst : 𝕃 (𝕃 char)) → l string≤list lst ≡ tt → list-is-sorted (l :: lst) ≡ list-is-sorted lst
helper-lemma [] [] l<lst = refl
helper-lemma [] (first :: rest) l<lst = refl
helper-lemma (x :: l) [] l<lst = refl
helper-lemma (x :: l) (first :: rest) l<lst rewrite l<lst = refl



output-wordst : ∀ (l : 𝕃 char) (t : Trie l) → l string≤list (wordst l t) ≡ tt

output-wordsl : ∀ (l : 𝕃 char) (lst : 𝕃 (Link l)) → (sortProof : IsSorted lst) → l string≤list (wordsl l lst sortProof) ≡ tt



output-wordst [] (node wordp children is-sorted) = empty-string≤ (wordst [] (node wordp children is-sorted))
output-wordst (x :: l) (node tt [] s[]) rewrite string-equality (x :: l) = refl
output-wordst (x :: l) (node ff [] s[]) = refl
output-wordst (x :: l) (node tt (first-link :: children) (fl<children s:: is-sorted)) rewrite output-wordsl (x :: l) (first-link :: children) (fl<children s:: is-sorted) | string-equality (x :: l) = refl
output-wordst (x :: l) (node ff (first-link :: children) (fl<children s:: is-sorted)) = output-wordsl (x :: l) (first-link :: children) (fl<children s:: is-sorted)

--output-wordsl : ∀ (l : 𝕃 char) (lst : 𝕃 (Link l)) → (sortProof : IsSorted lst) → l string≤list (wordsl l lst sortProof) ≡ tt
output-wordsl [] [] s[] = refl
output-wordsl [] (x :: lst) (newproof s:: sortproof) = empty-string≤ (wordsl [] (x :: lst) (newproof s:: sortproof))
output-wordsl (x :: l) [] s[] = refl
output-wordsl (x :: l) (link c child :: rest-link) (curr s:: sortproof) = string≤list-comm (x :: l) (wordst (x :: l ++ c :: []) child) (wordsl (x :: l) rest-link sortproof) ((string≤list+c (x :: l) c (wordst (x :: l ++ c :: []) child) (output-wordst (x :: l ++ c :: []) child))) (output-wordsl (x :: l) rest-link sortproof)



wordst+c<wordsl : ∀ (l : 𝕃 char)
                    (c : char)
                    (t : Trie (l ++ c :: []))
                    (linkc : Link l)
                    (lnks : 𝕃 (Link (l)))
                    (proofSorted : IsSorted lnks) -- need the other part of the proof
                    (firstSorted : linkc ≤* lnks)
                    → (wordst (l ++ c :: []) t) listwords≤listwords (wordsl l lnks proofSorted) ≡ tt
                    
wordst+c<wordsl l c t linkc lnks firstSorted proofSorted = {!!}



------------------------------------------------------------------------------------------

string≤list-fst : ∀ {w1 w2 : 𝕃 char} {lst : 𝕃 (𝕃 char)} → w1 string≤list (w2 :: lst) ≡ tt → w1 string≤ w2 ≡ tt
string≤list-fst {[]} {[]} {lst} p = refl
string≤list-fst {[]} {x :: w2} {lst} p = refl
string≤list-fst {x :: w1} {[]} {lst} ()
string≤list-fst {x :: w1} {y :: w2} {[]} p rewrite  (&&-tt (x =char2 y && w1 string≤ w2)) | &&-tt ((primCharToNat x < primCharToNat y || primCharToNat x =ℕ primCharToNat y && (w1 string≤ w2))) = p
string≤list-fst {x :: w1} {y :: w2} {lst :: rest} p rewrite (&&-fst {x <char3 y || (x =char2 y) && (w1 string≤ w2)} {((x :: w1) string≤ lst) && ((x :: w1) string≤list rest)} p) = refl


--maybe
firstlistwords≤ : ∀ {l1 l2 : 𝕃 (𝕃 char)} {w1 w2 : 𝕃 char} → (w1 :: l1) listwords≤listwords (w2 :: l2) ≡ tt → w1 string≤ w2 ≡ tt
firstlistwords≤ {l1} {l2} {w1} {w2} p1 = string≤list-fst {w1} {w2} {l2} (&&-fst {w1 string≤list (w2 :: l2)} {l1 listwords≤listwords (w2 :: l2)} p1) 


lstring1<lstring2-sort : ∀ {l1 l2 : 𝕃 (𝕃 char)} → l1 listwords≤listwords l2 ≡ tt → list-is-sorted l1 ≡ tt → list-is-sorted l2 ≡ tt → list-is-sorted (l1 ++ l2) ≡ tt
lstring1<lstring2-sort {[]} {[]} l1<l2 l1sort l2sort = refl
lstring1<lstring2-sort {[]} {l2 :: l3} l1<l2 l1sort l2sort = l2sort
lstring1<lstring2-sort {l1 :: l2} {[]} l1<l2 l1sort l2sort rewrite ++[] l2 = l1sort
lstring1<lstring2-sort {f1 :: l1} {f2 :: l2} l1<l2 l1sort l2sort = {!!}



-----------------------------------------------------------------------------------------

wordst-is-sorted : ∀ (l : 𝕃 char) (t : Trie l) → list-is-sorted (wordst l t) ≡ tt

wordsl-is-sorted : ∀ (l : 𝕃 char) (lst : 𝕃 (Link l)) (sortproof : IsSorted lst) → list-is-sorted (wordsl l lst sortproof) ≡ tt

wordst-is-sorted [] (node tt [] s[]) = refl
wordst-is-sorted [] (node ff [] s[]) = refl
wordst-is-sorted [] (node tt (link1 :: children) (first s:: rest)) rewrite cons-empty-sorting (wordsl [] (link1 :: children) (first s:: rest)) = wordsl-is-sorted [] (link1 :: children) (first s:: rest)
wordst-is-sorted [] (node ff (link1 :: children) (first s:: rest)) =  wordsl-is-sorted [] (link1 :: children) (first s:: rest)
wordst-is-sorted (x :: l) (node tt [] s[]) = refl
wordst-is-sorted (x :: l) (node ff [] s[]) = refl
wordst-is-sorted (x :: l) (node tt (link1 :: children) (firstp s:: restp)) rewrite output-wordsl (x :: l) (link1 :: children) (firstp s:: restp) = wordsl-is-sorted (x :: l) (link1 :: children) (firstp s:: restp)
wordst-is-sorted (x :: l) (node ff (link1 :: children) (firstp s:: restp)) = wordsl-is-sorted (x :: l) (link1 :: children) (firstp s:: restp)

wordsl-is-sorted [] [] s[] = refl
wordsl-is-sorted [] (link c child :: lnk) (first s:: restp) = {!!} {- lstring1<lstring2-sort {wordst (c :: []) child} {wordsl [] lnk restp} (wordst+c<wordsl [] c child lnk restp) (wordst-is-sorted (c :: []) child) (wordsl-is-sorted [] lnk restp) -}-- write a lemma about the append and the behavior on list is sorted
wordsl-is-sorted (x :: l) [] s[] = refl
wordsl-is-sorted (x :: l) (link c child :: rest-lnks) (firstp s:: restp) = {!!} {- lstring1<lstring2-sort {wordst (x :: l ++ c :: []) child} {wordsl (x :: l) rest-lnks restp} (wordst+c<wordsl (x :: l) c child rest-lnks restp) (wordst-is-sorted (x :: l ++ c :: []) child) (wordsl-is-sorted (x :: l) rest-lnks restp) -} -- use ^^^^^^^^^^ lemma to show this one


----------------------------------------------------------------------
-- tests 
----------------------------------------------------------------------

-- string≤
test-string≤ : ('a' :: 'b' :: 'c' :: []) string≤ ('a' :: 'b' :: 'c' :: []) ≡ tt
test-string≤ = refl

-- list-is-sorted
list-is-sorted-test1 : list-is-sorted (('a' :: []) :: ('b' :: []) :: ('c' :: []) :: ('d' :: []) :: []) ≡ tt
list-is-sorted-test1 = refl

list-is-sorted-test2 : list-is-sorted (('z' :: []) :: ('a' :: []) :: []) ≡ ff
list-is-sorted-test2 = refl

list-is-sorted-test3 : list-is-sorted (('a' :: 'b' :: 'c' :: []) :: ('a' :: 'b' :: 'd' :: []) :: []) ≡ tt
list-is-sorted-test3 = refl

list-is-sorted-test4 : list-is-sorted [] ≡ tt
list-is-sorted-test4 = refl

list-is-sorted-test5 : list-is-sorted ( ('a' :: 'p' :: 'p' :: []) :: ('a' :: 'p' :: 'p' :: 'l' :: 'e' :: []) :: []) ≡ tt
list-is-sorted-test5 = refl

list-is-sorted-test6 : list-is-sorted ( (string-to-𝕃char "apple") :: (string-to-𝕃char "applied") :: (string-to-𝕃char "devices") :: []) ≡ tt
list-is-sorted-test6 = refl

-- listword≤
testlistword≤ : ((string-to-𝕃char "apple") :: (string-to-𝕃char "applied") :: (string-to-𝕃char "devices") :: []) listwords≤listwords ((string-to-𝕃char "trying") :: (string-to-𝕃char "wonder") :: (string-to-𝕃char "zebra") :: []) ≡ tt
testlistword≤ = refl

testlistword≤2 : ((string-to-𝕃char "ab") :: (string-to-𝕃char "ac") :: (string-to-𝕃char "ad") :: []) listwords≤listwords ((string-to-𝕃char "aa") :: (string-to-𝕃char "ab") :: []) ≡ ff
testlistword≤2 = refl

-- string≤
teststring≤ : (string-to-𝕃char "ac") string≤ (string-to-𝕃char "ab") ≡ ff
teststring≤ = refl

-- trie 
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

-- Impossible to make a trie with the children not in order
--t4 : Trie []
--t4 = node ff ((link 'b'
--  (node tt [] s[])) :: (link 'a' (node tt [] s[])) :: []) (({!!} <:: {!!} {{!!}} {{!!}}) s:: {!!})

-- insert
trie-insert : Trie []
trie-insert = insert ('a' :: []) t0

-- wordst
wordst-test0 : wordst [] t0 ≡ []
wordst-test0 = refl

wordst-test1 : wordst [] t1 ≡ [] :: []
wordst-test1 = refl

wordst-test2 : wordst [] t2 ≡ ('a' :: []) :: []
wordst-test2 = refl

wordst-test : wordst [] t3 ≡ ('a' :: [])  :: ('o' :: 'n' :: []) :: []
wordst-test = refl

wordst-sorted-output-test : list-is-sorted (wordst [] t3) ≡ tt
wordst-sorted-output-test = refl

-- link-list-to-chars
link-list-to-chars-test : link-list-to-chars {[]} t3 ≡ ('a' :: 'o' :: [])
link-list-to-chars-test = refl

----------------------------------------------------------------------
-- helpful for later?
----------------------------------------------------------------------

-- <-trans : ∀ {x y z : ℕ} → x < y ≡ tt → y < z ≡ tt → x < z ≡ tt

{-

||-over-&&-l2 : ∀ {a b c : 𝔹} → a || (b && c) ≡ tt → (a || b) && (a || c) ≡ tt
||-over-&&-l2 {a} {b} {c} p rewrite ||-over-&&-l a b c = p


a-||-b-||-b : ∀ (a b : 𝔹) → (a || b) || b ≡ (a || b)
a-||-b-||-b tt tt = refl
a-||-b-||-b tt ff = refl
a-||-b-||-b ff tt = refl
a-||-b-||-b ff ff = refl

||-over-b : ∀ {a b : 𝔹} → (a || b) || b ≡ tt → (a || b) ≡ tt
||-over-b {a} {b} p rewrite a-||-b-||-b a b = p 


<char||=char : ∀ (c1 c2 : char) → (c1 <char2 c2) || (c1 =char2 c2) ≡ (c1 <char2 c2)
<char||=char c1 c2 = (a-||-b-||-b (primCharToNat c1 < primCharToNat c2) (primCharToNat c1 =ℕ primCharToNat c2))


-}

{-

reduction : ∀ (a b c : 𝔹) → (a || b) || b && c ≡ a || b
reduction tt tt tt = refl
reduction tt tt ff = refl
reduction tt ff tt = refl
reduction tt ff ff = refl
reduction ff tt tt = refl
reduction ff tt ff = refl
reduction ff ff tt = refl
reduction ff ff ff = refl

reductionP : ∀ {a b c : 𝔹} → (a || b) || b && c ≡ tt → a || b ≡ tt
reductionP {a} {b} {c} p rewrite reduction a b c = p

-}

{-
back-to-char< : ∀ (a b : char) → (primCharToNat a < primCharToNat b) || (primCharToNat a =ℕ primCharToNat b) ≡ a <char2 b
back-to-char< a b = refl

char<-to-back : ∀ (a b : char) → a <char2 b ≡ (primCharToNat a < primCharToNat b) || (primCharToNat a =ℕ primCharToNat b)
char<-to-back a b = refl

char<-to-P : ∀ {a b : char} → a <char2 b ≡ tt → (primCharToNat a < primCharToNat b) || (primCharToNat a =ℕ primCharToNat b) ≡ tt
char<-to-P {a} {b} p rewrite char<-to-back a b = p
-}

{-

Below is the goal

Goal: (x <char3 z) || (x =char2 z) && (l1 string≤ l3) ≡ tt
————————————————————————————————————————————————————————————
l2<l3 : (y <char3 z) || (y =char2 z) && (l2 string≤ l3) ≡ tt
l1<l2 : (x <char3 y) || (x =char2 y) && (l1 string≤ l2) ≡ tt

Each of these have the transitivity associated with it

Maybe make a decomp function?

-}

{-
decomp : ∀ (x y z : char) (l1 l2 l3 : 𝕃 char)
         → (x <char3 y) || (x =char2 y) && (l1 string≤ l2) ≡ tt
         → (y <char3 z) || (y =char2 z) && (l2 string≤ l3) ≡ tt
         → (x <char3 z) || (x =char2 z) && (l1 string≤ l3) ≡ tt
decomp x y z l1 l2 l3 p1 p2 = {!!}
-}

{-

<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 rewrite
  reduction (primCharToNat x < primCharToNat z) (primCharToNat x =ℕ primCharToNat z) (l1 string≤ l3) =  <char-trans {x} {y} {z} (reductionP { primCharToNat x < primCharToNat y } { primCharToNat x =ℕ primCharToNat y } { l1 string≤ l2 } l1<l2) (reductionP { primCharToNat y < primCharToNat z } { primCharToNat y =ℕ primCharToNat z } { l2 string≤ l3 } l2<l3)
-}

{-
string≤string+c2 : ∀ (l1 : 𝕃 char) (c : char) → l1 string≤ (l1 ++ c :: []) ≡ tt
string≤string+c2 [] c = refl
string≤string+c2 (x :: l) c rewrite char-refl x | ||-tt (primCharToNat x < primCharToNat x) = {!!}
-}


