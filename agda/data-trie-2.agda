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


_<char2_ : char → char → 𝔹
_<char2_ c1 c2 = (primCharToNat c1) ≤ (primCharToNat c2)


_=char2_ : char → char → 𝔹
_=char2_ c1 c2 = (primCharToNat c1) =ℕ (primCharToNat c2)

{-
postulate
  ≡char-to-= : (c1 c2 : char) → c1 ≡ c2 → _=char_ c1 c2 ≡ tt
  =char-to-≡ : (c1 c2 : char) → _=char_ c1 c2 ≡ tt → c1 ≡ c2
-}

{-
≡char-to-=2 : (c1 c2 : char) → c1 ≡ c2 → _=char2_ c1 c2 ≡ tt
≡char-to-=2 c1 c2 c1≡c2 = {!!}
-}



{-
<char3 : char → char → 𝔹
<char3 c1 c2 = (primCharToNat c1) ≤ (primCharToNat c2)
-}

{- Function that returns a boolean about whether a string is less than another string,
- Helper for list-is-sorted
-}
-- TODO check up on the function definitions here


{-
_string<_ : 𝕃 char → 𝕃 char → 𝔹
_string<_ [] [] = tt
_string<_ [] (x :: string2) = tt -- "" < "a : pple"
_string<_ (x :: string1) [] = ff -- "a : pple" < ""
_string<_ (x :: string1) (y :: string2) with x <char2 y
... | tt = tt -- "a : (pple)" < "b : (eets)"
... | ff with x =char y
... | tt =  string1 string< string2 -- if they are equal, recur on the next char "a : (pple)" = "a : (ble)" -> "p : (ple)" < "b : (le)"
... | ff = ff -- else case


-}


_string<_ : 𝕃 char → 𝕃 char → 𝔹
_string<_ [] [] = tt
_string<_ [] (x :: string2) = tt -- "" < "a : pple"
_string<_ (x :: string1) [] = ff -- "a : pple" < ""
_string<_ (x :: string1) (y :: string2) = (x <char2 y) || ((x =char2 y) && (string1 string< string2))





--(=𝕃 <char3 ('a' :: 'b' :: []) ('a' :: 'b' :: [])) 

{-
_string<_ : 𝕃 char → 𝕃 char → 𝔹
_string<_ [] [] = tt
_string<_ [] (x :: string2) = tt
_string<_ (x :: string1) [] = ff
_string<_ (x :: string1) (y :: string2) = (=𝕃 <char3 (x :: string1) (y :: string2))
-}


test-string< : ('a' :: 'b' :: 'c' :: []) string< ('a' :: 'b' :: 'c' :: []) ≡ tt
test-string< = refl


{- Function that returns a boolean about whether a string is less than all the other string in a list
- Helper for list-is-sorted
-}
-- given string, see if it is less than all other strings in the list


{-
_string<list_ : 𝕃 char → 𝕃 (𝕃 char) → 𝔹
_string<list_ [] [] = tt
_string<list_ [] (first-string :: rest-strings) = tt
_string<list_ (x :: comp-string) [] = tt
_string<list_ (x :: comp-string) (first-string :: rest-strings) with (x :: comp-string) string< first-string
... | tt = (x :: comp-string) string<list rest-strings
... | ff = ff

{- given list of strings, see if the list of strings is in the right order
              { Note: Useful for external verification? }
-}
list-is-sorted : 𝕃 (𝕃 char) → 𝔹
list-is-sorted [] = tt
list-is-sorted (first-string :: rest-of-words) with first-string string<list rest-of-words
... | tt = list-is-sorted rest-of-words
... | ff = ff

-}

_string<list_ : 𝕃 char → 𝕃 (𝕃 char) → 𝔹
_string<list_ [] [] = tt
_string<list_ [] (first-string :: rest-strings) = tt
_string<list_ (x :: comp-string) [] = tt
_string<list_ (x :: comp-string) (first-string :: rest-strings) = ((x :: comp-string) string< first-string) && ((x :: comp-string) string<list rest-strings)

{- given list of strings, see if the list of strings is in the right order
              { Note: Useful for external verification? }
-}
list-is-sorted : 𝕃 (𝕃 char) → 𝔹
list-is-sorted [] = tt
list-is-sorted (first-string :: rest-of-words)  = (first-string string<list rest-of-words) && (list-is-sorted rest-of-words)


list-of-chars-sorted : 𝕃 char → 𝔹
list-of-chars-sorted [] = tt
list-of-chars-sorted (x :: []) = tt
list-of-chars-sorted (x :: y :: l) = (x <char2 y) && list-of-chars-sorted (y :: l)




data Trie : 𝕃 char -> Set
data Link : 𝕃 char -> Set

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


{- to compute all of the words in `t` -}
wordst : ∀ l -> (t : Trie l) -> 𝕃 (𝕃 char)

{- to compute all of the words in `lst`, which are the children of some Trie -}
wordsl : ∀ l -> (lst : 𝕃 (Link l)) -> IsSorted lst → 𝕃 (𝕃 char)


wordst l (node tt children proof) = l :: (wordsl l children proof)
wordst l (node ff children proof) = wordsl l children proof
wordsl l [] s[] = []
wordsl l (link c child :: lt) (x s:: proof) = (wordst (l ++ (c :: [])) child) ++ (wordsl l lt proof)

test0 : wordst [] t0 ≡ []
test0 = refl

test1 : wordst [] t1 ≡ [] :: []
test1 = refl

test2 : wordst [] t2 ≡ ('a' :: []) :: []
test2 = refl

test : wordst [] t3 ≡ ('a' :: [])  :: ('o' :: 'n' :: []) :: []
test = refl


sort-test1 : list-is-sorted (('a' :: []) :: ('b' :: []) :: ('c' :: []) :: ('d' :: []) :: []) ≡ tt
sort-test1 = refl

sort-test2 : list-is-sorted (('z' :: []) :: ('a' :: []) :: []) ≡ ff
sort-test2 = refl

sort-test3 : list-is-sorted (('a' :: 'b' :: 'c' :: []) :: ('a' :: 'b' :: 'd' :: []) :: []) ≡ tt
sort-test3 = refl

sort-test4 : list-is-sorted [] ≡ tt
sort-test4 = refl

sort-test5 : list-is-sorted ( ('a' :: 'p' :: 'p' :: []) :: ('a' :: 'p' :: 'p' :: 'l' :: 'e' :: []) :: []) ≡ tt
sort-test5 = refl


sort-test6 : list-is-sorted ( (string-to-𝕃char "apple") :: (string-to-𝕃char "applied") :: (string-to-𝕃char "devices") :: []) ≡ tt
sort-test6 = refl


sorted-output : list-is-sorted (wordst [] t3) ≡ tt
sorted-output = refl



-- if IsSorted, then the rest are also sorted
{-
restSorted : ∀ (l : 𝕃 char) (lnk : Link l) (lstlnks : 𝕃 (Link l)) → IsSorted (lnk :: lstlnks) → IsSorted (lstlnks)
restSorted l lnk lstlnks (x s:: sortlnks) = sortlnks
-}



link-list-to-chars : ∀ {l : 𝕃 char} → Trie l → 𝕃 char
link-list-to-chars {l} (node wordp [] x) = []
link-list-to-chars {l} (node wordp (link c child :: children) (x s:: other)) = (c :: (link-list-to-chars {l} (node wordp children other)))

-- (c :: (link-list-to-chars {l} (node wordp children {!!})))


-- children-are-sorted : ∀ {l : 𝕃 char} → Trie l → list-is-sorte


link-list-test : link-list-to-chars {[]} t3 ≡ ('a' :: 'o' :: [])
link-list-test = refl


cons-empty-sorting : ∀ (l : 𝕃 (𝕃 char)) → list-is-sorted ([] :: l) ≡ list-is-sorted l
cons-empty-sorting [] = refl
cons-empty-sorting (l :: lst) = refl


empty-string-< : ∀ (lst : 𝕃 (𝕃 char)) → [] string<list lst ≡ tt
empty-string-< [] = refl
empty-string-< (lst :: lst₁) = refl



=string : 𝕃 char → 𝕃 char → 𝔹
=string [] [] = tt
=string [] (x :: l2) = ff
=string (x :: l1) [] = ff
=string (x1 :: l1) (x2 :: l2) = (x1 =char2 x2) && (=string l1 l2)

{-
=string2 : 𝕃 char → 𝕃 char → 𝔹
=string2 l1 l2 = ((𝕃char-to-string l1) =string (𝕃char-to-string l2))
-}

lemma-char : ∀ (l1 l2 : 𝕃 char) (c1 c2 : char) → =string (c1 :: l1) (c2 :: l2) ≡ tt → c1 =char2 c2 ≡ tt
lemma-char l1 l2 c1 c2 eqs = (&&-fst eqs)


{-
postulate
  ≡char-to-= : (c1 c2 : char) → c1 ≡ c2 → _=char_ c1 c2 ≡ tt
  =char-to-≡ : (c1 c2 : char) → _=char_ c1 c2 ≡ tt → c1 ≡ c2

-}

--=strin

{-
same-char= : ∀ (c : char) → c =char c ≡ tt
same-char= c = {!!}
-}




string-equality2 : ∀ (l1 l2 : 𝕃 char) → =string l1 l2 ≡ tt → l1 string< l2 ≡ tt
string-equality2 [] [] l1=l2 = refl
string-equality2 [] (x :: l2) ()
string-equality2 (x :: l1) [] ()
string-equality2 (x :: l1) (y :: l2) l1=l2 rewrite lemma-char l1 l2 x y l1=l2
                                                   | (string-equality2 l1 l2 (&&-snd l1=l2))
                                                   | ||-tt ((primCharToNat x) < (primCharToNat y)) = refl


-- ||-tt ((primCharToNat x) =ℕ (primCharToNat y)

{-
string-equality3 : ∀ (l1 l2 : 𝕃 char) → l1 ≡ l2 → l1 string< l2 ≡ tt
string-equality3 [] [] l1=l2 = refl
string-equality3 [] (x :: l2) ()
string-equality3 (x :: l1) [] ()
string-equality3 (x :: l1) (y :: l2) l1=l2 = {!!}
-}

------- maybe postulate ....



{-


=ℕ-refl : ∀ (x : ℕ) → (x =ℕ x) ≡ tt
=ℕ-refl 0 = refl
=ℕ-refl (suc x) = (=ℕ-refl x)

=ℕ-to-≡ : ∀ {x y : ℕ} → x =ℕ y ≡ tt → x ≡ y
=ℕ-to-≡ {0} {0} u = refl
=ℕ-to-≡ {suc x} {0} ()
=ℕ-to-≡ {0} {suc y} ()
=ℕ-to-≡ {suc x} {suc y} u rewrite =ℕ-to-≡ {x} {y} u = refl

=ℕ-from-≡ : ∀ {x y : ℕ} → x ≡ y → x =ℕ y ≡ tt
=ℕ-from-≡ {x} refl = =ℕ-refl x


-}



char-refl : ∀ (c : char) → (c =char2 c) ≡ tt
char-refl c = =ℕ-refl (primCharToNat c)


=string-refl : ∀ (l : 𝕃 char) → (=string l l) ≡ tt
=string-refl [] = refl
=string-refl (x :: l) rewrite char-refl (x) = (=string-refl l)




string-equality : ∀ (l : 𝕃 char) → l string< l ≡ tt
string-equality [] = refl
string-equality (x :: l) rewrite char-refl (x) | ||-tt ((primCharToNat x) < (primCharToNat x)) = refl

string<firstword-list : ∀ (l1 l2 : 𝕃 char) (stringList : 𝕃 (𝕃 char)) → (l1 string< l2) && (l1 string<list stringList) ≡ tt → l1 string<list (l2 :: stringList) ≡ tt
string<firstword-list [] [] [] proof = refl
string<firstword-list [] [] (stringList :: stringList₁) proof = refl
string<firstword-list [] (x :: l2) [] proof = refl
string<firstword-list [] (x :: l2) (stringList :: stringList₁) proof = refl
string<firstword-list (x :: l1) [] [] ()
string<firstword-list (x :: l1) [] (stringList :: stringList₁) ()
string<firstword-list (x :: l1) (x₁ :: l2) [] proof = proof
string<firstword-list (x :: l1) (x₁ :: l2) (stringList :: stringList₁) proof = proof

-- string<list

string<list-comm : ∀ (l : 𝕃 char) (l1 l2 : 𝕃 (𝕃 char)) → l string<list l1 ≡ tt → l string<list l2 ≡ tt → l string<list (l1 ++ l2) ≡ tt
string<list-comm [] [] [] l<l1 l<l2 = refl
string<list-comm (x :: l) [] [] l<l1 l<l2 = refl
string<list-comm [] [] (lchars2 :: lchars3) l<l1 l<l2 = refl
string<list-comm (x :: l) [] (lchars2 :: lchars3) l<l1 l<l2 = l<l2
string<list-comm [] (lchars1 :: lchars2) [] l<l1 l<l2 = refl
string<list-comm (x :: l) (lchars1 :: lchars2) [] l<l1 l<l2 rewrite ++[] lchars2 = l<l1
string<list-comm [] (lchars1 :: lchars2) (lchars3 :: lchars4) l<l1 l<l2 = refl
string<list-comm (x :: l) (firstString :: lchars2) (secondString :: lchars4) l<l1 l<l2 rewrite
  &&-fst {(x :: l) string< firstString} {(x :: l) string<list lchars2} l<l1
  = string<list-comm (x :: l) lchars2 (secondString :: lchars4) (&&-snd {(x :: l) string< firstString} {(x :: l) string<list lchars2} l<l1)  (string<firstword-list (x :: l) secondString lchars4 l<l2)


helper-string<lemma : ∀ (l : 𝕃 char) (c : char) → =string l l ≡ tt → l string< (l ++ c :: []) ≡ tt
helper-string<lemma [] c proof = refl
helper-string<lemma (x :: l) c proof rewrite &&-fst { (x =char2 x) } { =string l l } proof | ||-tt (primCharToNat x < primCharToNat x) = refl

=char-trans : ∀ {c1 c2 c3 : char} → c1 =char2 c2 ≡ tt → c2 =char2 c3 ≡ tt → c1 =char2 c3 ≡ tt
=char-trans {c1} {c2} {c3} p1 p2 rewrite
  =ℕ-to-≡ {primCharToNat c1} {primCharToNat c2} p1
  | =ℕ-to-≡ {primCharToNat c2} {primCharToNat c3} p2 = =ℕ-refl (primCharToNat c3)



<char-trans : ∀ {c1 c2 c3 : char} → c1 <char2 c2 ≡ tt → c2 <char2 c3 ≡ tt → c1 <char2 c3 ≡ tt
<char-trans {c1} {c2} {c3} p1 p2 = {!!}


<string-trans : ∀ (l1 l2 l3 : 𝕃 char) → l1 string< l2 ≡ tt → l2 string< l3 ≡ tt → l1 string< l3 ≡ tt
<string-trans [] [] [] l1<l2 l2<l3 = refl
<string-trans [] [] (x :: l3) l1<l2 l2<l3 = refl
<string-trans [] (x :: l2) [] l1<l2 l2<l3 = refl
<string-trans [] (x :: l2) (x₁ :: l3) l1<l2 l2<l3 = refl
<string-trans (x :: l1) [] [] ()
<string-trans (x :: l1) [] (x₁ :: l3) ()
<string-trans (x :: l1) (x₁ :: l2) [] l1<l2 ()
<string-trans (x :: l1) (y :: l2) (z :: l3) l1<l2 l2<l3 rewrite ||-over-&&-l (x <char2 z) (x =char2 z) (l1 string< l3)= {!!}

string<string+c2 : ∀ (l1 : 𝕃 char) (c : char) → l1 string< (l1 ++ c :: []) ≡ tt
string<string+c2 [] c = refl
string<string+c2 (x :: l) c rewrite char-refl x | ||-tt (primCharToNat x < primCharToNat x) = refl


string<string+c : ∀ (l1 l2 : 𝕃 char) (c : char) → (l1 ++ c :: []) string< l2 ≡ tt → (l1 string< l2) ≡ tt
string<string+c [] [] c proof = refl
string<string+c [] (x :: l2) c proof = refl
string<string+c (x :: l1) [] c ()
string<string+c (x :: l1) (firstchar :: l2) c proof = {!!}

{-

proof     : (x <char2 firstchar) ||
            (x =char2 firstchar) && ((l1 ++ c :: []) string< l2)
            ≡ tt

-}
-- rewrite ||-over-&&-l (x <char2 firstchar) (x =char2 firstchar) (l1 string< l2)

-- &&-fst {(x <char2 firstchar) || (x =char firstchar)} {l1 string< l2} proof


string<list+c : ∀ (l : 𝕃 char) (c : char) (lst : 𝕃 (𝕃 char)) → (l ++ c :: []) string<list lst ≡ tt → l string<list lst ≡ tt
string<list+c [] c [] proof = refl
string<list+c [] c (lst :: lst₁) proof = refl
string<list+c (x :: l) c [] proof = refl
string<list+c (x :: l) c (first :: rest) proof rewrite string<string+c (x :: l) (first) c (&&-fst proof) = string<list+c (x :: l) c rest (&&-snd proof)


{-
≡-to-=string : (s1 s2 : 𝕃 char) → s1 ≡ s2 → =string s1 s2 ≡ tt
≡-to-=string [] [] s1=s2 = refl
≡-to-=string [] (x :: s2) ()
≡-to-=string (x :: s1) [] ()
≡-to-=string (x :: s1) (y :: s2) s1=s2 = {!!}
-}


output-wordst : ∀ (l : 𝕃 char) (t : Trie l) → l string<list (wordst l t) ≡ tt

output-wordsl : ∀ (l : 𝕃 char) (lst : 𝕃 (Link l)) → (sortProof : IsSorted lst) → l string<list (wordsl l lst sortProof) ≡ tt


{-
output-wordst+c : ∀ (l : 𝕃 char) (c : char) (t : Trie (l ++ c :: [])) → l string<list (wordst (l ++ c :: []) t) ≡ tt
output-wordst+c l c t = {!!}
-}

-- output-combined : ∀ (l : 𝕃 char) (c : char) (t : Trie (l ++ c :: []) 


output-wordst [] (node wordp children is-sorted) = empty-string-< (wordst [] (node wordp children is-sorted))
output-wordst (x :: l) (node tt [] s[]) rewrite string-equality (x :: l) = refl
output-wordst (x :: l) (node ff [] s[]) = refl
output-wordst (x :: l) (node tt (first-link :: children) (fl<children s:: is-sorted)) rewrite output-wordsl (x :: l) (first-link :: children) (fl<children s:: is-sorted) | string-equality (x :: l) = refl
output-wordst (x :: l) (node ff (first-link :: children) (fl<children s:: is-sorted)) = output-wordsl (x :: l) (first-link :: children) (fl<children s:: is-sorted)

--output-wordsl : ∀ (l : 𝕃 char) (lst : 𝕃 (Link l)) → (sortProof : IsSorted lst) → l string<list (wordsl l lst sortProof) ≡ tt
output-wordsl [] [] s[] = refl
output-wordsl [] (x :: lst) (newproof s:: sortproof) = empty-string-< (wordsl [] (x :: lst) (newproof s:: sortproof))
output-wordsl (x :: l) [] s[] = refl
output-wordsl (x :: l) (link c child :: rest-link) (curr s:: sortproof) = string<list-comm (x :: l) (wordst (x :: l ++ c :: []) child) (wordsl (x :: l) rest-link sortproof) ((string<list+c (x :: l) c (wordst (x :: l ++ c :: []) child) (output-wordst (x :: l ++ c :: []) child))) (output-wordsl (x :: l) rest-link sortproof)


{-

Goal: ((x :: l) string<list
       (wordst (x :: l ++ c :: []) child ++
        wordsl (x :: l) rest-link sortproof))
      ≡ tt


provide proof that: 

p1 : (x :: l) string<list (wordst (x :: l ++ c :: []) child)




p1 : (string<list+c (x :: l) c (wordst (x :: l ++ c :: []) child) (output-wordst (x :: l ++ c :: []) child))

say that l < 

p2 : output-wordsl (x :: l) rest-link sortproof

combine them as such:


string<list-comm (x :: l) (wordst (x :: l ++ c :: []) child) (wordst (x :: l) rest-link sortproof) p1 p2







-}



-- empty-string-< (wordsl [] (x :: lst) {!!})



-- need lemmas about the behavior of wordst in given conditions
-- need lemmas about the behavior of wordsl in given conditions


{-

{- to compute all of the words in `t` -}
wordst : ∀ l -> (t : Trie l) -> 𝕃 (𝕃 char)

{- to compute all of the words in `lst`, which are the children of some Trie -}
wordsl : ∀ l -> (lst : 𝕃 (Link l)) -> IsSorted lst → 𝕃 (𝕃 char)


wordst l (node tt children proof) = l :: (wordsl l children proof)
wordst l (node ff children proof) = wordsl l children proof
wordsl l [] s[] = []
wordsl l (link c child :: lt) (x s:: proof) = (wordst (l ++ (c :: [])) child) ++ (wordsl l lt proof)

-}

{-
append-[]= : ∀ (l : 𝕃 char) → l ≡ (l ++ [])
append-[]= [] = refl
append-[]= (x :: l) = {!refl!}
-}




-- &&-snd {(x :: l) string< firstString} {(x :: l) string<list lchars2} l<l1 --- first argument
-- string<firstword-list (x :: l) secondString lchars4 l<l2 --- second argument



-- wordst l (node tt children proof) = l :: wordsl l children ------> from the defining equations this should work

-- something like this...

{-
equate-wordst-wordsl : ∀ (l : 𝕃 char) → (t : Trie l) → (lnk : 𝕃 (Link l)) → (sortProof : (IsSorted lnk)) → wordst l t ≡ l :: wordsl l lnk sortProof
equate-wordst-wordsl = {!!}



children-are-next-level : ∀ (l : 𝕃 char) → (t : Trie l) → {- wordst l t -} 𝔹
children-are-next-level = {!!}
-}


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
wordsl-is-sorted [] (x :: lnk) (first s:: restp) = {!!}
wordsl-is-sorted (x :: l) [] s[] = refl
wordsl-is-sorted (x :: l) (first-link :: rest-lnks) (firstp s:: restp) = {!!}



{-

final-sort [] (node tt [] s[]) = refl
final-sort [] (node ff [] s[]) = refl
final-sort [] (node tt (link1 :: children) (first s:: rest)) rewrite cons-empty-sorting (wordsl [] (link1 :: children)) = final-sortsl [] (link1 :: children) 
final-sort [] (node ff (link1 :: children) (first s:: rest)) = final-sortsl [] (link1 :: children)    -------------------------------------------------- ^^^^ These two are now the same case
final-sort (x :: l) (node tt [] s[]) = refl
final-sort (x :: l) (node ff [] s[]) = refl
final-sort (x :: l) (node tt (link1 :: children) (first s:: rest)) rewrite helper-lemma (x :: l) (wordsl ( x :: l) (link1 :: children)) ((helper-2-lemma (x :: l) link1 children first)) = final-sortsl (x :: l) (link1 :: children)
final-sort (x :: l) (node ff (link1 :: children) (first s:: rest)) = final-sortsl (x :: l) (link1 :: children)



final-sortsl [] [] = refl
final-sortsl [] (link c child :: rest-links) = {!!}
final-sortsl (x :: l) [] = refl
final-sortsl (x :: l) (link c child :: rest-links) = {!!}


-}


{-
{-
sorted-lemma : ∀ {l : 𝕃 char} {lnk : 𝕃 (Link l)} {t : Trie l} → IsSorted lnk → list-is-sorted (wordst l t) ≡ tt
sorted-lemma {l} {lnk} {t} sorted = {!!}
-}

-- for any trie, wordst of that trie is sorted

--final-sort : ∀ {l : 𝕃 char} → (t : Trie l) → (lst : wordst l t) → list-is-sorted lst ≡ tt
--final-sort = ?

cons-empty-sorting : ∀ (l : 𝕃 (𝕃 char)) → list-is-sorted ([] :: l) ≡ list-is-sorted l
cons-empty-sorting [] = refl
cons-empty-sorting (l :: lst) = refl


--<*lemma : link l ≤* 𝕃 link l → c1 from link l

{-
_link<_ : ∀ {l : 𝕃 char} → Link l → Link l → 𝔹
_link<_ {l} (link c1 child1) (link c2 child2) = c1 <char2 c2
-}

other-helper-lemma : ∀ (lst : 𝕃 (𝕃 char)) → [] string<list lst ≡ tt
other-helper-lemma [] = refl
other-helper-lemma (lst :: lst₁) = refl

helper-lemma : ∀ (l : 𝕃 char) (lst : 𝕃 (𝕃 char)) → l string<list lst ≡ tt → list-is-sorted (l :: lst) ≡ list-is-sorted lst
helper-lemma [] [] l<lst = refl
helper-lemma [] (first :: rest) l<lst = refl
helper-lemma (x :: l) [] l<lst = refl
helper-lemma (x :: l) (first :: rest) l<lst rewrite l<lst = refl

-- want to say that the efirst of the output of wordst (l ++ c :: []) will contain c


append-empty :  ∀ (l : 𝕃 char) (lst : 𝕃 (𝕃 char)) → l string<list (lst ++ []) ≡ l string<list lst
append-empty [] [] = refl
append-empty [] (first :: rest) = refl
append-empty (x :: l) [] = refl
append-empty (x :: l) (first :: rest) with (x :: l) string< first
... | tt = append-empty (x :: l) rest
... | ff = refl


--helper-5-lemma : ∀ (l : 𝕃 char) → (t : Trie (l)) → wordst l t ≡ wordsl l 
--helper-5-lemma = ?

-- wordst l (node ff children proof) = wordsl l children
-- children is a 𝕃 links type l

-- l :: wordsl l children


-- wordst : ∀ l -> (t : Trie l) -> 𝕃 (𝕃 char)

helper-5-lemma : ∀ (l : 𝕃 char) (c : char) (t : (Trie (l ++ c :: []))) → l string<list (wordst (l ++ c :: []) t) ≡ tt
helper-5-lemma [] c t = other-helper-lemma (wordst (c :: []) t)
helper-5-lemma (x :: l) c t with keep ((x :: l) string< (head (wordst ((x :: l) ++ c :: []) t ) {!!}))
... | tt , xl<f = {!!}
... | ff , ()

-- define the behavior of wordst for a given l and l further

helper-4-lemma : ∀ (l : 𝕃 char) (c : char) (child : Trie (l ++ c :: [])) → l string<list (wordst (l ++ c :: []) child ++ []) ≡ tt
helper-4-lemma [] c child = other-helper-lemma (wordst (c :: []) child ++ [])
helper-4-lemma (x :: l) c (node wordp [] s[]) rewrite append-empty (x :: l) (wordst (x :: l ++ c :: []) (node wordp [] s[])) = {!!}
helper-4-lemma (x :: l) c (node wordp (first-link :: children) isSorted) rewrite append-empty (x :: l) (wordst (x :: l ++ c :: []) (node wordp (first-link :: children) isSorted))  = {!!}



final-sort : ∀ (l : 𝕃 char) (t : Trie l) → list-is-sorted (wordst l t) ≡ tt
final-sortsl : ∀ (l : 𝕃 char) (lst : 𝕃 (Link l)) → list-is-sorted (wordsl l lst) ≡ tt



sorting-lemma : ∀ (c : char)
                (l : 𝕃 char)
                (child : Trie (l ++ c :: []))
                (rest-links : 𝕃 (Link l))
                → l string<list ((wordst (l ++ c :: []) child) ++ (wordsl l rest-links)) ≡ tt
sorting-lemma c [] child rest-links = other-helper-lemma (wordst (c :: []) child ++ wordsl [] rest-links)
sorting-lemma c (x :: l) child rest-links = {!!}


helper-2-lemma : ∀ (l : 𝕃 char) → (lnk : Link l) → (children : 𝕃 (Link l)) → lnk ≤* children → l string<list (wordsl l) (lnk :: children) ≡ tt
helper-2-lemma [] lnk children lnk<children = other-helper-lemma (wordsl [] (lnk :: children))
helper-2-lemma (x :: l) (link c child) [] <[] = helper-4-lemma (x :: l) c child
helper-2-lemma (x :: l) (link c child) (first-link :: children) (lnk <:: lnk<children) = sorting-lemma c (x :: l) child (first-link :: children) 

final-sort [] (node tt [] s[]) = refl
final-sort [] (node ff [] s[]) = refl
final-sort [] (node tt (link1 :: children) (first s:: rest)) rewrite cons-empty-sorting (wordsl [] (link1 :: children)) = final-sortsl [] (link1 :: children) 
final-sort [] (node ff (link1 :: children) (first s:: rest)) = final-sortsl [] (link1 :: children)    -------------------------------------------------- ^^^^ These two are now the same case
final-sort (x :: l) (node tt [] s[]) = refl
final-sort (x :: l) (node ff [] s[]) = refl
final-sort (x :: l) (node tt (link1 :: children) (first s:: rest)) rewrite helper-lemma (x :: l) (wordsl ( x :: l) (link1 :: children)) ((helper-2-lemma (x :: l) link1 children first)) = final-sortsl (x :: l) (link1 :: children)
final-sort (x :: l) (node ff (link1 :: children) (first s:: rest)) = final-sortsl (x :: l) (link1 :: children)



{-

([] string<list
       (wordst (c :: []) child ++ wordsl [] rest-links))
      ≡ tt

-}


{-
Goal: list-is-sorted
      (wordst (c :: []) child ++ wordsl [] rest-links)
      ≡ tt
-}

final-sortsl [] [] = refl
final-sortsl [] (link c child :: rest-links) = {!!}
final-sortsl (x :: l) [] = refl
final-sortsl (x :: l) (link c child :: rest-links) = {!!}

-}

{-
list-is-sorted
      (wordst (c :: []) child ++ wordsl [] rest-links)
      ≡ tt
-}

{-
Goal: list-is-sorted
      (wordst [] (node tt (link1 :: children) (first s:: rest)))
      ≡ tt


Goal: (list-is-sorted 
      ([] :: wordsl [] (link1 :: children))
       | [] string<list wordsl [] (link1 :: children))
      ≡ tt

-}

