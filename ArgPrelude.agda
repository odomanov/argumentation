module ArgPrelude where

open import Agda.Builtin.Float
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Empty
open import Data.Float public hiding (_==_; _-_; _+_)
open import Data.Integer hiding (_*_)
open import Data.List
open import Data.Maybe
open import Data.Nat as ℕ using (suc; ℕ; _∸_; _⊔_)
open import Data.Product 
open import Data.String as S using (String) renaming (_++_ to _+++_)
open import Data.Unit
open import Function using (id)
open import Level public renaming (zero to lzero; suc to lsuc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality public using (_≡_; _≢_; refl)
open import Relation.Nullary

open import WLPretty public

-- boolean equality

record BEq {ℓ} (A : Set ℓ): Set (lsuc ℓ) where
  field
    _===_ : A → A → Bool
    -- isEquivalence = IsEquivalence _===_

open BEq {{...}} public

-- boolean filter

filterb : ∀ {ℓ} {A : Set ℓ} → (P : A → Bool) → List A → List A
filterb P [] = []
filterb P (x ∷ xs) with P x
... | true = x ∷ filterb P xs
... | false = filterb P xs



-- preliminary

data Proposition : Set where
  mkProp : String → Proposition
  NOT    : Proposition → Proposition
  _AND_  : Proposition → Proposition → Proposition
  _OR_   : Proposition → Proposition → Proposition

private
  _=P_ : Proposition → Proposition → Bool
  (mkProp x) =P (mkProp y) = x S.== y
  NOT x      =P NOT y      = x =P y
  (x₁ AND x₂)  =P (y₁ AND y₂)  = (x₁ =P y₁) ∧ (x₂ =P y₂) 
  (x₁ OR  x₂)  =P (y₁ OR  y₂)  = (x₁ =P y₁) ∧ (x₂ =P y₂)
  _ =P _ = false

infix 4 _≡P_ _≟P_

_≡P_ : Proposition → Proposition → Set
(mkProp x) ≡P (mkProp y) = x ≡ y
NOT x      ≡P NOT y      = x ≡P y
(x₁ AND x₂)  ≡P (y₁ AND y₂)  = (x₁ ≡P y₁) × (x₂ ≡P y₂) 
(x₁ OR  x₂)  ≡P (y₁ OR  y₂)  = (x₁ ≡P y₁) × (x₂ ≡P y₂)
_ ≡P _ = ⊥

_≟P_ : Decidable _≡P_
(mkProp x) ≟P (mkProp y) = x S.≟ y
NOT x      ≟P NOT y      = x ≟P y
(x₁ AND x₂)  ≟P (y₁ AND y₂)  with (x₁ ≟P y₁) | (x₂ ≟P y₂)
... | yes p₁ | yes p₂ = yes (p₁ , p₂)
... | yes _  | no ¬p₂ = no λ x → ¬p₂ (proj₂ x)
... | no ¬p₁ | yes _  = no λ x → ¬p₁ (proj₁ x)
... | no ¬p₁ | no  _  = no λ x → ¬p₁ (proj₁ x) 
(x₁ OR  x₂)  ≟P (y₁ OR  y₂)  with (x₁ ≟P y₁) | (x₂ ≟P y₂)
... | yes p₁ | yes p₂ = yes (p₁ , p₂)
... | yes _  | no ¬p₂ = no λ x → ¬p₂ (proj₂ x)
... | no ¬p₁ | yes _  = no λ x → ¬p₁ (proj₁ x)
... | no ¬p₁ | no  _  = no λ x → ¬p₁ (proj₁ x) 
(mkProp _) ≟P NOT _ = no id
(mkProp _) ≟P _ AND _ = no id
(mkProp _) ≟P _ OR _ = no id
(NOT _) ≟P (mkProp _) = no id
(NOT _) ≟P _ AND _ = no id
(NOT _) ≟P _ OR _ = no id
(_ AND _) ≟P (mkProp _) = no id
(_ AND _) ≟P NOT _ = no id
(_ AND _) ≟P _ OR _ = no id
(_ OR _) ≟P (mkProp _) = no id
(_ OR _) ≟P NOT _ = no id
(_ OR _) ≟P _ AND _ = no id

instance
  PEq : BEq Proposition
  _===_ {{PEq}} x y = x =P y


-- Statement consists of Proposition and a particular text this proposition is stated in.
record Statement : Set where
  constructor st
  field
    sttext : Maybe String  -- the statement text
    stprop : Proposition   -- it's meaning (proposition)

infix 4 _≡S_ _≟S_

_≡S_ : Statement → Statement → Set
x ≡S y = (Statement.stprop x) ≡P (Statement.stprop y)

_≟S_ : Decidable _≡S_
x ≟S y = (Statement.stprop x) ≟P (Statement.stprop y)


-- bool equality
private
  _=S_ : Statement → Statement → Bool
  (st _ x) =S (st _ y) = x =P y

instance
  SEq : BEq Statement
  _===_ {{SEq}} x y = x =S y




-- float arithmetics

infix 5 _[<]_ _[≤]_ _[=]_
infixl 6 _[+]_ _[-]_ 
infixl 7 _[*]_

_[+]_ : Float → Float → Float 
x [+] y = primFloatPlus x y
_[-]_ : Float → Float → Float 
x [-] y = primFloatMinus x y
_[*]_ : Float → Float → Float 
x [*] y = primFloatTimes x y
_[/]_ : Float → Float → Float 
x [/] y = primFloatDiv x y
_[=]_ : Float → Float → Bool
x [=] y = primFloatEquality x y
_[<]_ : Float → Float → Bool 
x [<] y = primFloatLess x y
_[≤]_ : Float → Float → Bool 
x [≤] y = primFloatLess x y ∨ primFloatEquality x y 


-- Some Docs

docSection : ℕ → String → Doc
docSection n s = line <> text (s +++ "  ")
                 <> text (S.replicate (0 ℕ.⊔ ((n ∸ 2) ∸ S.length s)) '=')

docFloat : Float → Doc
docFloat x = text (Data.Float.show x)

-- rounded to 3 decimal places
docFloatRounded : Float → Doc
docFloatRounded x = text (Data.Float.show ((primRound (x * 1000.0)) /1000))
  where
  _/1000 : ℤ → Float
  (+ n) /1000 = (primNatToFloat n) ÷ 1000.0
  (-[1+ n ]) /1000 = primFloatNegate ((primNatToFloat (n ∸ 1)) ÷ 1000.0)


