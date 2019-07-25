-- Label Algebra (Budan et al.)

module LabelAlgebra where

open import Algebra.FunctionProperties
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary

record IsLabelAlgebra {c ℓ₁ ℓ₂} {A : Set c}
                         (_≈_ : Rel A ℓ₁)
                         (_≤_ : Rel A ℓ₂)
                         (_⊙_ : Op₂ A)
                         (_⊕_ : Op₂ A)
                         (_⊖_ : Op₂ A)
                         (⊘ : Op₁ A)
                         (⊤ : A)
                         (⊥ : A)
                         : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    isPOrder  : IsPartialOrder _≈_ _≤_ 
    maximum   : Maximum _≤_ ⊤
    minimum   : Minimum _≤_ ⊥
    -- support
    ⊙-comm    : Commutative _≈_ _⊙_
    ⊙-mono    : ∀ (p q r) → p ≤ q → (p ⊙ r) ≤ (q ⊙ r) --  Monotone 
    ⊙-assoc   : Associative _≈_ _⊙_
    ⊙-neut    : ∀ (a) → (a ⊙ ⊤) ≈ a
    -- aggregation    
    ⊕-comm    : Commutative _≈_ _⊕_
    ⊕-mono    : ∀ (p q r) → p ≤ q → (p ⊕ r) ≤ (q ⊕ r) --  Monotone 
    ⊕-assoc   : Associative _≈_ _⊕_
    ⊕-neut    : ∀ (a) → (a ⊕ ⊥) ≈ a
    -- conflict
    ⊖-1       : ∀ (a b) → b ≤ a → ¬ a ≈ b → (a ⊖ b) ≤ a
    ⊖-2       : ∀ (a b) → a ≤ b → (a ⊖ b) ≈ ⊥
    ⊖-mono    : ∀ (p q r) → p ≤ q → (p ⊖ r) ≤ (q ⊖ r) --  Monotone 
    ⊖-neut    : ∀ (a) → (a ⊖ ⊥) ≈ a
    ⊖-3       : ∀ (a b) → (a ⊖ b) ≈ ⊥ → (b ⊖ a) ≈ ⊥ → a ≈ b
    ⊖-4       : ∀ (a b) → (a ⊕ b) ≤ ⊤ → ¬ ((a ⊕ b) ≈ ⊤) → ((a ⊕ b) ⊖ b) ≈ a

record LabelAlgebra c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 6 _⊕_
  infixr 7 _⊖_
  infixr 7 _⊙_
  field
    Carrier   : Set c
    _≈_       : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_       : Rel Carrier ℓ₂  -- The partial order.
    _⊙_       : Op₂ Carrier     -- The support operation.
    _⊕_       : Op₂ Carrier     -- The aggregation operation.
    _⊖_       : Op₂ Carrier     -- The conflict operation.
    ⊘         : Op₁ Carrier     -- The negation operation.
    ⊤         : Carrier         -- The maximum.
    ⊥         : Carrier         -- The minimum.
    isLabelAlgebra : IsLabelAlgebra _≈_ _≤_ _⊙_ _⊕_ _⊖_ ⊘ ⊤ ⊥ 
    
  open IsLabelAlgebra isLabelAlgebra public

open LabelAlgebra public
