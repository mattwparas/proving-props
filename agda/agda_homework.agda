
module _ where

{-
 1. Do exercises 1.1 and 1.2 in the text.

1.1:
 (a) evaluates to tt
 (b) evalutes to ff
 (c) evalutes to ff
1.2:
 (a) 𝔹
 (b) 𝔹
 (c) 𝔹 -> 𝔹 -> 𝔹
 (d) Set
-}

open import bool
open import eq
open import nat



{- 

   Fill in the body of the isadd2 function 
   so that `add2 b1 b2 b3 b4 = tt`
   if and only if the two digit binary
   number b1,b2 is equal to the two digit 
   binary number b3,b4 plus 1. For example,

   isadd2 ff tt ff ff = tt
  
   since b1,b2 = 1, b3,b4 = 0, and 0+1 = 1, but 

   isadd2 tt ff tt tt = ff

   since b1,b2 = 2, b3, b4 = 3, and 3+1 =/= 2
-}

{-
∀ {l : Level} -> {A : Set l} -> 𝔹 -> A -> A -> A
-}


_,_ : 𝔹 -> 𝔹 -> ℕ
ff , ff = 0
ff , tt = 1
tt , ff = 2
tt , tt = 3

{- identify where true all else are false -}
isadd2 : 𝔹 -> 𝔹 -> 𝔹 -> 𝔹 -> 𝔹
isadd2 tt tt tt tt = ff
isadd2 tt tt tt ff = tt
isadd2 tt tt ff tt = ff
isadd2 tt tt ff ff = ff
isadd2 tt ff tt tt = ff
isadd2 tt ff tt ff = ff
isadd2 tt ff ff tt = tt
isadd2 tt ff ff ff = ff
isadd2 ff tt tt tt = ff
isadd2 ff tt tt ff = ff
isadd2 ff tt ff tt = ff
isadd2 ff tt ff ff = tt
isadd2 ff ff tt tt = ff
isadd2 ff ff tt ff = ff
isadd2 ff ff ff tt = ff
isadd2 ff ff ff ff = ff




{- for UBool (possibly unknown bools)
   think of `TT` and `FF` as values that
   are completely known, but `??` as a value
   that might be true and might be false,
   but we do not know yet (think: we are waiting
   for the electricity to flow to this point
   in the ciruit)
-}
   
data MBool : Set where
   TT : MBool
   FF : MBool
   ?? : MBool



{- there are sometimes functions that return known values when they
   get an unknown value, but sometimes their answer is not known
   yet. For example, when `Mand` sees a false, it knows the answer, no
   matter if the other argument is known or not. But when it 
   gets a true in one argument and the unknown input in the other,
   it must propogate the unknown value. -}

Mand : MBool -> MBool -> MBool
Mand FF _ = FF
Mand _ FF = FF
Mand TT mb = mb
Mand mb TT = mb
Mand ?? ?? = ??

{- Implement Mor. -}

Mor : MBool -> MBool -> MBool
Mor TT _ = TT
Mor _ TT = TT
Mor FF FF = FF
Mor FF mb = mb
Mor mb FF = mb
Mor ?? ?? = ??


{- We can prove the theorems about the relationship between Mand and
   regular booleans if we lift from MBools to bools.  -}

lift : bool -> MBool
lift tt = TT
lift ff = FF




andlift : ∀ b1 b2 →  Mand (lift b1) (lift b2) ≡ lift (b1 && b2)
andlift tt tt = refl
andlift tt ff = refl
andlift ff tt = refl
andlift ff ff = refl

orlift : ∀ b1 b2 →  Mor (lift b1) (lift b2) ≡ lift (b1 || b2)
orlift tt tt = refl
orlift tt ff = refl
orlift ff tt = refl
orlift ff ff = refl

