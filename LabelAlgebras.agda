-- Using Labels for reasoning. Definitions of Label algebras
-- TODO: Prove 0≤v⊙ etc.

module LabelAlgebras where

open import Data.Bool
open import Data.Empty
open import Data.Maybe
open import Data.Nat
open import Data.String renaming (_++_ to _+++_)
open import Data.Unit
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import ArgPrelude

open import LabelAlgebra public
  renaming (⊤ to LA⊤; ⊥ to LA⊥; _∧_ to _LA∧_; _∨_ to _LA∨_)

-- Float interval [0..1]
record FUnit : Set where
  constructor mkFUnit
  field
    value : Float
    0≤v   : (0.0 [≤] value) ≡ true
    v≤1   : (value [≤] 1.0) ≡ true

open FUnit public

V : (x : Float) → {p1 : 0.0 [≤] x ≡ true} → {p2 : x [≤] 1.0 ≡ true} → FUnit
V x {p1} {p2} = record { value = x; 0≤v = p1; v≤1 = p2 }

FU0 : FUnit
FU0 = record { value = 0.0; 0≤v = refl; v≤1 = refl }

FU1 : FUnit
FU1 = record { value = 1.0; 0≤v = refl; v≤1 = refl }

FU= : FUnit → FUnit → Set
FU= a b = value a ≡ value b

FU< : FUnit → FUnit → Set
FU< a b = if (value a) [<] (value b) then ⊤ else ⊥ 

FU≤ : FUnit → FUnit → Set
FU≤ a b = if (value a) [≤] (value b) then ⊤ else ⊥ 


fmin : Float → Float → Float
fmin x y = if x [<] y then x else y 

fmax : Float → Float → Float
fmax x y = if x [<] y then y else x 

postulate
  0≤vmean : ∀ x y → 0.0 [≤] (0.5 [*] (value x [+] value y)) ≡ true
  v≤1mean : ∀ x y → (0.5 [*] (value x [+] value y)) [≤] 1.0 ≡ true

FUmean : FUnit → FUnit → FUnit 
FUmean a b = record
  { value = 0.5 [*] (value a [+] value b) 
  ; 0≤v = 0≤vmean a b 
  ; v≤1 = v≤1mean a b 
  }


postulate
  0≤½v : ∀ x → (0.0 [≤] (0.5 [*] (value x))) ≡ true  
  ½v≤1 : ∀ x → (0.5 [*] (value x) [≤] 1.0) ≡ true   

min0≤v : ∀ x y → (0.0 [≤] (fmin (value x) (value y)) ≡ true)
min0≤v x y with (value x) [<] (value y)
min0≤v (mkFUnit _ 0≤v₁ _) y | true = 0≤v₁
min0≤v x (mkFUnit _ 0≤v₁ _) | false = 0≤v₁

minv≤1 : ∀ x y → (fmin (value x) (value y)) [≤] 1.0 ≡ true
minv≤1 x y with (value x) [<] (value y)
minv≤1 (mkFUnit _ _ v≤2) y | true = v≤2
minv≤1 x (mkFUnit _ _ v≤2) | false = v≤2

max0≤v : ∀ x y → (0.0 [≤] (fmax (value x) (value y)) ≡ true)
max0≤v x y with (value x) [<] (value y)
max0≤v x (mkFUnit _ 0≤v₁ _) | true = 0≤v₁
max0≤v (mkFUnit _ 0≤v₁ _) y | false = 0≤v₁

maxv≤1 : ∀ x y → (fmax (value x) (value y)) [≤] 1.0 ≡ true
maxv≤1 x y with (value x) [<] (value y)
maxv≤1 x (mkFUnit _ _ v≤2) | true = v≤2
maxv≤1 (mkFUnit _ _ v≤2) y | false = v≤2



-------------------------------------------------------
-- Trust Algebra

postulate
  0≤v⊙ : ∀ x y → 0.0 [≤] (value x) [*] (value y) ≡ true
  v≤1⊙ : ∀ x y → (value x) [*] (value y) [≤] 1.0 ≡ true

-- 0≤v⊙ : ∀ x y → 0.0 [≤] (value x) [*] (value y) ≡ true
-- 0≤v⊙ (mkFUnit value₁ 0≤v₁ v≤2) (mkFUnit value₂ 0≤v₂ v≤3) = {!0≤v₁!}

-- 0≤v⊙ : ∀ {x y} (v) → {_ : v ≡ (value x) [*] (value y)} → 0.0 [≤] v ≡ true
-- 0≤v⊙ {mkFUnit value₁ 0≤v₁ v≤2} {mkFUnit value₂ 0≤v₂ v≤3} v {p} = {!0≤v₁!}

Trust⊙ : FUnit → FUnit → FUnit
Trust⊙ a b = record
  { value = (value a) [*] (value b)
  ; 0≤v = 0≤v⊙ a b
  ; v≤1 = v≤1⊙ a b
  }

postulate
  0≤v⊕ : ∀ x y → 0.0 [≤] ((x [+] y) [-] (x [*] y)) ≡ true
  v≤1⊕ : ∀ x y → ((x [+] y) [-] (x [*] y)) [≤] 1.0 ≡ true

Trust⊕ : FUnit → FUnit → FUnit
Trust⊕ a b = record
  { value = (value a) [+] (value b) [-] ((value a) [*] (value b))
  ; 0≤v = 0≤v⊕ (value a) (value b)
  ; v≤1 = v≤1⊕ (value a) (value b)
  }

-- value⊖ : Float → Float → Float
-- value⊖ a b with 1.0 [=] a | 1.0 [=] b
-- ... | true  | false = 1.0
-- ... | false | _ with (a [<] b) ∨ not (a [=] b) | 1.0 [=] b
-- ...            | true | false = ((a [-] b) [/] (1.0 [-] b))
-- ...            | _    | _     = 0.0
-- value⊖ _ _ | _ | _ = 0.0

-- postulate
--   0≤v⊖ : ∀ x y → 0.0 [≤] (value⊖ x y) ≡ true
--   v≤1⊖ : ∀ x y → (value⊖ x y) [≤] 1.0 ≡ true

-- Trust⊖ : FUnit → FUnit → FUnit
-- Trust⊖ a b = record
--   { value = value⊖ (value a) (value b)
--   ; 0≤v = 0≤v⊖ (value a) (value b)
--   ; v≤1 = v≤1⊖ (value a) (value b)
--   }

postulate
  0≤v⊘ : ∀ x → 0.0 [≤] (value FU1) [-] value x ≡ true
  v≤1⊘ : ∀ x → (value FU1) [-] value x [≤] 1.0 ≡ true

Trust⊘ : FUnit → FUnit
Trust⊘ a = record
  { value = (value FU1) [-] (value a)
  ; 0≤v = 0≤v⊘ a
  ; v≤1 = v≤1⊘ a 
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
    FU= FU≤ Trust⊙ Trust⊕ -- Trust⊖
    Trust⊘ Trust∧ Trust∨ FUmean FU1 FU0

docTrust : FUnit → Doc
docTrust (mkFUnit x _ _) = docFloatRounded x

Trust : LabelAlgebra _ _ _
Trust = record
  { Carrier = FUnit
  ; _≈_ = FU=
  ; _≤_ = FU≤
  ; _⊙_ = Trust⊙
  ; _⊕_ = Trust⊕
  -- ; _⊖_ = Trust⊖
  ; ⊘   = Trust⊘
  ; _∧_ = Trust∧
  ; _∨_ = Trust∨
  ; mean = FUmean
  ; ⊤ = FU1
  ; ⊥ = FU0
  ; isLabelAlgebra = Trust-isLabelAlgebra
  ; doc = docTrust
  }




-------------------------------------------------------
-- Preference Algebra

Pref⊙ : FUnit → FUnit → FUnit
Pref⊙ a b = record
  { value = fmin (value a) (value b)
  ; 0≤v = min0≤v a b 
  ; v≤1 = minv≤1 a b 
  }

postulate
  pref0≤v⊕ : ∀ x y → 0.0 [≤] (fmin (value x [+] value y) 1.0) ≡ true
  prefv≤1⊕ : ∀ x y → (fmin (value x [+] value y) 1.0) [≤] 1.0 ≡ true

Pref⊕ : FUnit → FUnit → FUnit
Pref⊕ a b = record
  { value = fmin (value a [+] value b) 1.0
  ; 0≤v = pref0≤v⊕ a b 
  ; v≤1 = prefv≤1⊕ a b 
  }

-- postulate
--   pref0≤v⊖ : ∀ x y → 0.0 [≤] (fmax ((value x) [-] (value y)) 0.0) ≡ true
--   prefv≤1⊖ : ∀ x y → (fmax ((value x) [-] (value y)) 0.0) [≤] 1.0 ≡ true

-- Pref⊖ : FUnit → FUnit → FUnit
-- Pref⊖ a b = record
--   { value = fmax ((value a) [-] (value b)) 0.0
--   ; 0≤v = pref0≤v⊖ a b 
--   ; v≤1 = prefv≤1⊖ a b 
--   }

Pref⊘ : FUnit → FUnit
Pref⊘ a = record
  { value = (value FU1) [-] (value a)
  ; 0≤v = 0≤v⊘ a 
  ; v≤1 = v≤1⊘ a 
  }

Pref∨ : FUnit → FUnit → FUnit
Pref∨ a b = record
  { value = fmax (value a) (value b)
  ; 0≤v = max0≤v a b
  ; v≤1 = maxv≤1 a b
  }

Pref½ : FUnit → FUnit
Pref½ x = record
  { value = 0.5 [*] (value x)
  ; 0≤v = 0≤½v x
  ; v≤1 = ½v≤1 x
  }

postulate
  Pref-isLabelAlgebra : IsLabelAlgebra
    FU= FU≤ Pref⊙ Pref⊕ -- Pref⊖
    Pref⊘ Pref⊙ Pref∨ FUmean FU1 FU0

docPref : FUnit → Doc
docPref (mkFUnit x _ _) = docFloatRounded x 

Pref : LabelAlgebra _ _ _
Pref = record
  { Carrier = FUnit
  ; _≈_ = FU=
  ; _≤_ = FU≤
  ; _⊙_ = Pref⊙
  ; _⊕_ = Pref⊕
  -- ; _⊖_ = Pref⊖
  ; ⊘   = Pref⊘
  ; _∧_ = Pref⊙
  ; _∨_ = Pref∨
  ; mean = FUmean
  ; ⊤ = FU1
  ; ⊥ = FU0
  ; isLabelAlgebra = Pref-isLabelAlgebra
  ; doc = docPref
  }



-------------------------------------------------------
-- Łukasiewicz Algebra

postulate
  luk0≤v⊙ : ∀ x y → 0.0 [≤] (fmax 0.0 ((value x) [+] (value y) [-] 1.0)) ≡ true
  lukv≤1⊙ : ∀ x y → (fmax 0.0 ((value x) [+] (value y) [-] 1.0)) [≤] 1.0 ≡ true

Łuk⊙ : FUnit → FUnit → FUnit
Łuk⊙ a b = record
  { value = fmax 0.0 ((value a) [+] (value b) [-] 1.0)
  ; 0≤v = luk0≤v⊙ a b 
  ; v≤1 = lukv≤1⊙ a b 
  }

postulate
  luk0≤v⊕ : ∀ x y → 0.0 [≤] (fmin (value x [+] value y) 1.0) ≡ true
  lukv≤1⊕ : ∀ x y → (fmin (value x [+] value y) 1.0) [≤] 1.0 ≡ true

Łuk⊕ : FUnit → FUnit → FUnit
Łuk⊕ a b = record
  { value = fmin (value a [+] value b) 1.0
  ; 0≤v = luk0≤v⊕ a b 
  ; v≤1 = lukv≤1⊕ a b 
  }

Łuk⊘ : FUnit → FUnit
Łuk⊘ a = record
  { value = (value FU1) [-] (value a)
  ; 0≤v = 0≤v⊘ a 
  ; v≤1 = v≤1⊘ a 
  }

Łuk∧ : FUnit → FUnit → FUnit
Łuk∧ a b = record
  { value = fmin (value a) (value b)
  ; 0≤v = min0≤v a b
  ; v≤1 = minv≤1 a b
  }

Łuk∨ : FUnit → FUnit → FUnit
Łuk∨ a b = record
  { value = fmax (value a) (value b)
  ; 0≤v = max0≤v a b
  ; v≤1 = maxv≤1 a b
  }

Łuk½ : FUnit → FUnit
Łuk½ x = record
  { value = 0.5 [*] (value x)
  ; 0≤v = 0≤½v x
  ; v≤1 = ½v≤1 x
  }

postulate
  Łuk-isLabelAlgebra : IsLabelAlgebra
    FU= FU≤ Łuk⊙ Łuk⊕ -- Łuk⊖
    Łuk⊘ Łuk∧ Łuk∨ FUmean FU1 FU0

docŁuk : FUnit → Doc
docŁuk (mkFUnit x _ _) = docFloatRounded x 

Łuk : LabelAlgebra _ _ _
Łuk = record
  { Carrier = FUnit
  ; _≈_ = FU=
  ; _≤_ = FU≤
  ; _⊙_ = Łuk⊙
  ; _⊕_ = Łuk⊕
  -- ; _⊖_ = Łuk⊖
  ; ⊘   = Łuk⊘
  ; _∧_ = Łuk∧
  ; _∨_ = Łuk∨
  ; mean = FUmean
  ; ⊤ = FU1
  ; ⊥ = FU0
  ; isLabelAlgebra = Łuk-isLabelAlgebra
  ; doc = docŁuk
  }


-------------------------------------------------------
-- Gödel t-norm

-- postulate
--   göd0≤v⊙ : ∀ x y → 0.0 [≤] (fmin (value x) (value y)) ≡ true
--   gödv≤1⊙ : ∀ x y → (fmax 0.0 ((value x) [+] (value y) [-] 1.0)) [≤] 1.0 ≡ true

Göd⊙ : FUnit → FUnit → FUnit
Göd⊙ a b = record
  { value = fmin (value a) (value b)
  ; 0≤v = min0≤v a b 
  ; v≤1 = minv≤1 a b 
  }

-- postulate
--   göd0≤v⊕ : ∀ x y → 0.0 [≤] (fmin (value x [+] value y) 1.0) ≡ true
--   gödv≤1⊕ : ∀ x y → (fmin (value x [+] value y) 1.0) [≤] 1.0 ≡ true

Göd⊕ : FUnit → FUnit → FUnit
Göd⊕ a b = record
  { value = fmax (value a) (value b)
  ; 0≤v = max0≤v a b 
  ; v≤1 = maxv≤1 a b 
  }

Göd⊘ : FUnit → FUnit
Göd⊘ a = record
  { value = (value FU1) [-] (value a)
  ; 0≤v = 0≤v⊘ a 
  ; v≤1 = v≤1⊘ a 
  }

Göd∧ = Göd⊙
Göd∨ = Göd⊕

-- Göd∧ : FUnit → FUnit → FUnit
-- Göd∧ a b = record
--   { value = fmin (value a) (value b)
--   ; 0≤v = min0≤v a b
--   ; v≤1 = minv≤1 a b
--   }

-- Göd∨ : FUnit → FUnit → FUnit
-- Göd∨ a b = record
--   { value = fmax (value a) (value b)
--   ; 0≤v = max0≤v a b
--   ; v≤1 = maxv≤1 a b
--   }

Göd½ : FUnit → FUnit
Göd½ x = record
  { value = 0.5 [*] (value x)
  ; 0≤v = 0≤½v x
  ; v≤1 = ½v≤1 x
  }

postulate
  Gödel-isLabelAlgebra : IsLabelAlgebra
    FU= FU≤ Göd⊙ Göd⊕ -- Göd⊖
    Göd⊘ Göd∧ Göd∨ FUmean FU1 FU0

docGödel : FUnit → Doc
docGödel (mkFUnit x _ _) = docFloatRounded x 

Gödel : LabelAlgebra _ _ _
Gödel = record
  { Carrier = FUnit
  ; _≈_ = FU=
  ; _≤_ = FU≤
  ; _⊙_ = Göd⊙
  ; _⊕_ = Göd⊕
  -- ; _⊖_ = Göd⊖
  ; ⊘   = Göd⊘
  ; _∧_ = Göd∧
  ; _∨_ = Göd∨
  ; mean = FUmean
  ; ⊤ = FU1
  ; ⊥ = FU0
  ; isLabelAlgebra = Gödel-isLabelAlgebra
  ; doc = docGödel
  }


