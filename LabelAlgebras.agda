-- Using Labels for reasoning. Definitions of Label algebras
-- TODO Prove 0≤v⊙ etc.

module LabelAlgebras where

open import Agda.Builtin.Float
open import Data.Bool
open import Data.Empty
open import Data.Float
open import Data.Maybe
open import Data.String renaming (_++_ to _+++_)
open import Data.Unit
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import LabelAlgebra public renaming (⊤ to LA⊤; ⊥ to LA⊥)

_LessEq_ : Float → Float → Bool
x LessEq y = (primFloatLess x y ∨ primFloatEquality x y)

record FUnit : Set where
  constructor mkFUnit
  field
    value : Float
    0≤v   : (0.0 LessEq value) ≡ true
    v≤1   : (value LessEq 1.0) ≡ true

open FUnit

FU0 : FUnit
FU0 = record { value = 0.0; 0≤v = refl; v≤1 = refl }

FU1 : FUnit
FU1 = record { value = 1.0; 0≤v = refl; v≤1 = refl }

FUEquality : FUnit → FUnit → Set
FUEquality a b = value a ≡ value b

FULess : FUnit → FUnit → Set
FULess a b = if (primFloatLess (value a) (value b)) then ⊤ else ⊥ 

FULessEq : FUnit → FUnit → Set
FULessEq a b = if (value a) LessEq (value b) then ⊤ else ⊥ 


-------------------------------------------------------
-- Trust Algebra

postulate
  0≤v⊙ : ∀ x y → 0.0 LessEq (primFloatTimes x y) ≡ true
  v≤1⊙ : ∀ x y → (primFloatTimes x y) LessEq 1.0 ≡ true

Trust⊙ : FUnit → FUnit → FUnit
Trust⊙ a b = record
  { value = primFloatTimes (value a) (value b)
  ; 0≤v = 0≤v⊙ (value a) (value b)
  ; v≤1 = v≤1⊙ (value a) (value b)
  }

postulate
  0≤v⊕ : ∀ x y → 0.0 LessEq (primFloatMinus (primFloatPlus x y) (primFloatTimes x y)) ≡ true
  v≤1⊕ : ∀ x y → (primFloatMinus (primFloatPlus x y) (primFloatTimes x y)) LessEq 1.0 ≡ true

Trust⊕ : FUnit → FUnit → FUnit
Trust⊕ a b = record
  { value = primFloatMinus (primFloatPlus (value a) (value b))
                           (primFloatTimes (value a) (value b))
  ; 0≤v = 0≤v⊕ (value a) (value b)
  ; v≤1 = v≤1⊕ (value a) (value b)
  }

value⊖ : Float → Float → Float
value⊖ a b with primFloatEquality 1.0 a | primFloatEquality 1.0 b
... | true  | false = 1.0
... | false | _ with primFloatLess a b ∨ not (primFloatEquality a b) | primFloatEquality 1.0 b
...            | true | false = (primFloatDiv (primFloatMinus a b) (primFloatMinus 1.0 b))
...            | _    | _     = 0.0
value⊖ _ _ | _ | _ = 0.0

postulate
  0≤v⊖ : ∀ x y → 0.0 LessEq (value⊖ x y) ≡ true
  v≤1⊖ : ∀ x y → (value⊖ x y) LessEq 1.0 ≡ true

Trust⊖ : FUnit → FUnit → FUnit
Trust⊖ a b = record
  { value = value⊖ (value a) (value b)
  ; 0≤v = 0≤v⊖ (value a) (value b)
  ; v≤1 = v≤1⊖ (value a) (value b)
  }

postulate
  Trust-isLabelAlgebra : IsLabelAlgebra FUEquality FULessEq Trust⊙ Trust⊕ Trust⊖ FU1 FU0

Trust : LabelAlgebra _ _ _
Trust = record
  { Carrier = FUnit
  ; _≈_ = FUEquality
  ; _≤_ = FULessEq
  ; _⊙_ = Trust⊙
  ; _⊕_ = Trust⊕
  ; _⊖_ = Trust⊖
  ; ⊤ = FU1
  ; ⊥ = FU0
  ; isLabelAlgebra = Trust-isLabelAlgebra
  }

TV : (x : Float) → {p1 : 0.0 LessEq x ≡ true} → {p2 : x LessEq 1.0 ≡ true}
     → LabelAlgebra.Carrier Trust
TV x {p1} {p2} = record { value = x; 0≤v = p1; v≤1 = p2 }


-------------------------------------------------------
-- Preference Algebra

fmin : Float → Float → Float
fmin x y with primFloatLess x y 
... | true  = x
... | false = y

fmax : Float → Float → Float
fmax x y with primFloatLess x y 
... | true  = y
... | false = x

postulate
  pref0≤v⊙ : ∀ x y → (0.0 LessEq (fmin (value x) (value y)) ≡ true)
  prefv≤1⊙ : ∀ x y → (fmin (value x) (value y)) LessEq 1.0 ≡ true

Pref⊙ : FUnit → FUnit → FUnit
Pref⊙ a b = record
  { value = fmin (value a) (value b)
  ; 0≤v = pref0≤v⊙ a b 
  ; v≤1 = prefv≤1⊙ a b 
  }

postulate
  pref0≤v⊕ : ∀ x y → 0.0 LessEq (fmin (primFloatPlus (value x) (value y)) 1.0) ≡ true
  prefv≤1⊕ : ∀ x y → (fmin (primFloatPlus (value x) (value y)) 1.0) LessEq 1.0 ≡ true

Pref⊕ : FUnit → FUnit → FUnit
Pref⊕ a b = record
  { value = fmin (primFloatPlus (value a) (value b)) 1.0
  ; 0≤v = pref0≤v⊕ a b 
  ; v≤1 = prefv≤1⊕ a b 
  }

postulate
  pref0≤v⊖ : ∀ x y → 0.0 LessEq (fmax (primFloatMinus (value x) (value y)) 0.0) ≡ true
  prefv≤1⊖ : ∀ x y → (fmax (primFloatMinus (value x) (value y)) 0.0) LessEq 1.0 ≡ true

Pref⊖ : FUnit → FUnit → FUnit
Pref⊖ a b = record
  { value = fmax (primFloatMinus (value a) (value b)) 0.0
  ; 0≤v = pref0≤v⊖ a b 
  ; v≤1 = prefv≤1⊖ a b 
  }

postulate
  Pref-isLabelAlgebra : IsLabelAlgebra FUEquality FULessEq Pref⊙ Pref⊕ Pref⊖ FU1 FU0

Pref : LabelAlgebra _ _ _
Pref = record
  { Carrier = FUnit
  ; _≈_ = FUEquality
  ; _≤_ = FULessEq
  ; _⊙_ = Pref⊙
  ; _⊕_ = Pref⊕
  ; _⊖_ = Pref⊖
  ; ⊤ = FU1
  ; ⊥ = FU0
  ; isLabelAlgebra = Pref-isLabelAlgebra
  }

PV : (x : Float) → {p1 : 0.0 LessEq x ≡ true} → {p2 : x LessEq 1.0 ≡ true}
     → LabelAlgebra.Carrier Pref
PV x {p1} {p2} = record { value = x; 0≤v = p1; v≤1 = p2 }

P≡FU : Carrier Pref ≡ FUnit
P≡FU = refl

_ : Maybe FUnit ≡ Maybe (Carrier Pref)
_ = refl



-- for printing

showFUnit : Maybe FUnit → String
showFUnit nothing = "NOTHING"
showFUnit (just (mkFUnit x _ _)) = Data.Float.show x

showLabelPref : Maybe (LabelAlgebra.Carrier Pref) → String
showLabelPref v = showFUnit v

showLabelTrust : Maybe (LabelAlgebra.Carrier Trust) → String
showLabelTrust v = showFUnit v

-- showLabel : ∀ {c ℓ₁ ℓ₂} (la : LabelAlgebra c ℓ₁ ℓ₂) → Maybe (LabelAlgebra.Carrier la) → String
-- showLabel {c = lzero} Pref v = showLabelPref v 
-- showLabel Trust v = showLabelTrust v 
-- showLabel Pref v rewrite P≡FU = (showLabelPref v) 
-- showLabel Pref (just (mkFUnit v _ _)) = Data.Float.show v 
