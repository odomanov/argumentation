-- Using Labels for reasoning. Definitions of Label algebras
-- TODO: Prove 0≤v⊙ etc.

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

open import LabelAlgebra public
  renaming (⊤ to LA⊤; ⊥ to LA⊥; _∧_ to _LA∧_; _∨_ to _LA∨_)

_LessEq_ : Float → Float → Bool
x LessEq y = (primFloatLess x y ∨ primFloatEquality x y)

-- Float interval [0..1]
record FUnit : Set where
  constructor mkFUnit
  field
    value : Float
    0≤v   : (0.0 LessEq value) ≡ true
    v≤1   : (value LessEq 1.0) ≡ true

open FUnit public

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


fmin : Float → Float → Float
fmin x y with primFloatLess x y 
... | true  = x
... | false = y

fmax : Float → Float → Float
fmax x y with primFloatLess x y 
... | true  = y
... | false = x

postulate
  ½0≤v : ∀ x → (0.0 LessEq primFloatTimes 0.5 (value x)) ≡ true  
  ½v≤1 : ∀ x → (primFloatTimes 0.5 (value x) LessEq 1.0) ≡ true   

min0≤v : ∀ x y → (0.0 LessEq (fmin (value x) (value y)) ≡ true)
min0≤v x y with primFloatLess (value x) (value y)
min0≤v (mkFUnit _ 0≤v₁ _) y | true = 0≤v₁
min0≤v x (mkFUnit _ 0≤v₁ _) | false = 0≤v₁

minv≤1 : ∀ x y → (fmin (value x) (value y)) LessEq 1.0 ≡ true
minv≤1 x y with primFloatLess (value x) (value y)
minv≤1 (mkFUnit _ _ v≤2) y | true = v≤2
minv≤1 x (mkFUnit _ _ v≤2) | false = v≤2

max0≤v : ∀ x y → (0.0 LessEq (fmax (value x) (value y)) ≡ true)
max0≤v x y with primFloatLess (value x) (value y)
max0≤v x (mkFUnit _ 0≤v₁ _) | true = 0≤v₁
max0≤v (mkFUnit _ 0≤v₁ _) y | false = 0≤v₁

maxv≤1 : ∀ x y → (fmax (value x) (value y)) LessEq 1.0 ≡ true
maxv≤1 x y with primFloatLess (value x) (value y)
maxv≤1 x (mkFUnit _ _ v≤2) | true = v≤2
maxv≤1 (mkFUnit _ _ v≤2) y | false = v≤2



-------------------------------------------------------
-- Trust Algebra

postulate
  0≤v⊙ : ∀ x y → 0.0 LessEq (primFloatTimes (value x) (value y)) ≡ true
  v≤1⊙ : ∀ x y → (primFloatTimes (value x) (value y)) LessEq 1.0 ≡ true

-- 0≤v⊙ : ∀ x y → 0.0 LessEq (primFloatTimes (value x) (value y)) ≡ true
-- 0≤v⊙ (mkFUnit value₁ 0≤v₁ v≤2) (mkFUnit value₂ 0≤v₂ v≤3) = {!0≤v₁!}

-- 0≤v⊙ : ∀ {x y} (v) → {_ : v ≡ primFloatTimes (value x) (value y)} → 0.0 LessEq v ≡ true
-- 0≤v⊙ {mkFUnit value₁ 0≤v₁ v≤2} {mkFUnit value₂ 0≤v₂ v≤3} v {p} = {!0≤v₁!}

Trust⊙ : FUnit → FUnit → FUnit
Trust⊙ a b = record
  { value = primFloatTimes (value a) (value b)
  ; 0≤v = 0≤v⊙ a b
  ; v≤1 = v≤1⊙ a b
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

-- postulate
--   0≤v⊖ : ∀ x y → 0.0 LessEq (value⊖ x y) ≡ true
--   v≤1⊖ : ∀ x y → (value⊖ x y) LessEq 1.0 ≡ true

-- Trust⊖ : FUnit → FUnit → FUnit
-- Trust⊖ a b = record
--   { value = value⊖ (value a) (value b)
--   ; 0≤v = 0≤v⊖ (value a) (value b)
--   ; v≤1 = v≤1⊖ (value a) (value b)
--   }

postulate
  0≤v⊘ : ∀ x → 0.0 LessEq (primFloatMinus (value FU1) x) ≡ true
  v≤1⊘ : ∀ x → (primFloatMinus (value FU1) x) LessEq 1.0 ≡ true

Trust⊘ : FUnit → FUnit
Trust⊘ a = record
  { value = primFloatMinus (value FU1) (value a)
  ; 0≤v = 0≤v⊘ (value a) 
  ; v≤1 = v≤1⊘ (value a) 
  }

Trust∧ : FUnit → FUnit → FUnit
Trust∧ a b = record
  { value = fmin (value a) (value b)
  ; 0≤v = min0≤v a b
  ; v≤1 = minv≤1 a b
  }

Trust∨ : FUnit → FUnit → FUnit
Trust∨ a b = record
  { value = fmax (value a) (value b)
  ; 0≤v = max0≤v a b
  ; v≤1 = maxv≤1 a b
  }

Trust½ : FUnit → FUnit
Trust½ x = x                       -- dummy definition !!

postulate
  Trust-isLabelAlgebra : IsLabelAlgebra
    FUEquality FULessEq Trust⊙ Trust⊕ -- Trust⊖
      Trust⊘ Trust∧ Trust∨ Trust½ FU1 FU0

Trust : LabelAlgebra _ _ _
Trust = record
  { Carrier = FUnit
  ; _≈_ = FUEquality
  ; _≤_ = FULessEq
  ; _⊙_ = Trust⊙
  ; _⊕_ = Trust⊕
  -- ; _⊖_ = Trust⊖
  ; ⊘   = Trust⊘
  ; _∧_ = Trust∧
  ; _∨_ = Trust∨
  ; ½   = Trust½
  ; ⊤ = FU1
  ; ⊥ = FU0
  ; isLabelAlgebra = Trust-isLabelAlgebra
  }

TV : (x : Float) → {p1 : 0.0 LessEq x ≡ true} → {p2 : x LessEq 1.0 ≡ true}
     → LabelAlgebra.Carrier Trust
TV x {p1} {p2} = record { value = x; 0≤v = p1; v≤1 = p2 }




-------------------------------------------------------
-- Preference Algebra

Pref⊙ : FUnit → FUnit → FUnit
Pref⊙ a b = record
  { value = fmin (value a) (value b)
  ; 0≤v = min0≤v a b 
  ; v≤1 = minv≤1 a b 
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

-- postulate
--   pref0≤v⊖ : ∀ x y → 0.0 LessEq (fmax (primFloatMinus (value x) (value y)) 0.0) ≡ true
--   prefv≤1⊖ : ∀ x y → (fmax (primFloatMinus (value x) (value y)) 0.0) LessEq 1.0 ≡ true

-- Pref⊖ : FUnit → FUnit → FUnit
-- Pref⊖ a b = record
--   { value = fmax (primFloatMinus (value a) (value b)) 0.0
--   ; 0≤v = pref0≤v⊖ a b 
--   ; v≤1 = prefv≤1⊖ a b 
--   }

Pref⊘ : FUnit → FUnit
Pref⊘ a = record
  { value = primFloatMinus (value FU1) (value a)
  ; 0≤v = 0≤v⊘ (value a) 
  ; v≤1 = v≤1⊘ (value a) 
  }

Pref∨ : FUnit → FUnit → FUnit
Pref∨ a b = record
  { value = fmax (value a) (value b)
  ; 0≤v = max0≤v a b
  ; v≤1 = maxv≤1 a b
  }

Pref½ : FUnit → FUnit
Pref½ x = record
  { value = primFloatTimes 0.5 (value x)
  ; 0≤v = ½0≤v x
  ; v≤1 = ½v≤1 x
  }

postulate
  Pref-isLabelAlgebra : IsLabelAlgebra
    FUEquality FULessEq Pref⊙ Pref⊕ -- Pref⊖
      Pref⊘ Pref⊙ Pref∨ Pref½ FU1 FU0

Pref : LabelAlgebra _ _ _
Pref = record
  { Carrier = FUnit
  ; _≈_ = FUEquality
  ; _≤_ = FULessEq
  ; _⊙_ = Pref⊙
  ; _⊕_ = Pref⊕
  -- ; _⊖_ = Pref⊖
  ; ⊘   = Pref⊘
  ; _∧_ = Pref⊙
  ; _∨_ = Pref∨
  ; ½   = Pref½
  ; ⊤ = FU1
  ; ⊥ = FU0
  ; isLabelAlgebra = Pref-isLabelAlgebra
  }

PV : (x : Float) → {p1 : 0.0 LessEq x ≡ true} → {p2 : x LessEq 1.0 ≡ true}
     → LabelAlgebra.Carrier Pref
PV x {p1} {p2} = record { value = x; 0≤v = p1; v≤1 = p2 }

