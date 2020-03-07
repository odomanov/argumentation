module ArgPrelude where

open import Agda.Builtin.Float
open import Agda.Builtin.Nat
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Bool.Show using (show)
open import Data.Empty
open import Data.Float public
open import Data.List
open import Data.Maybe
open import Data.Nat as ℕ using (suc; ℕ; _∸_; _⊔_)
open import Data.Nat.Show
open import Data.String as S using (String) renaming (_++_ to _+++_)
open import Data.Unit
open import Function using (id)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary

open import WLPretty public

-- boolean equality

record BEq {ℓ} (A : Set ℓ): Set (lsuc ℓ) where
  field
    _===_ : A → A → Bool
    -- beqrefl  : ∀ x → x === x ≡ true
    -- beqtrans : ∀ x y z → x === y ≡ true → y === z ≡ true → x === z ≡ true
    -- beqsymm  : ∀ x y → x === y ≡ true → y === x ≡ true
    -- isEquivalence = IsEquivalence _===_

open BEq {{...}} public

-- boolean filter

filterb : ∀ {ℓ} {A : Set ℓ} → (P : A → Bool) → List A → List A
filterb P [] = []
filterb P (x ∷ xs) with P x
... | true = x ∷ filterb P xs
... | false = filterb P xs



-- preliminary

record Thesis' : Set where
  constructor th'
  field
    pos : String  -- positive form
    neg : String  -- negative form

data Thesis : Set where
  Pos : Thesis' → Thesis  -- тезис
  Neg : Thesis' → Thesis  -- отрицание тезиса
  Th  : String  → Thesis  -- если отрицание не определено / не требуется

-- bool equality
_=T_ : Thesis → Thesis → Bool
(Pos x) =T (Pos y) = (Thesis'.pos x) S.== (Thesis'.pos y)
(Neg x) =T (Neg y) = (Thesis'.pos x) S.== (Thesis'.pos y)
(Th x) =T (Th y) = x S.== y
_ =T _ = false

infix 4 _≟T_

private
  _≡T_ : Thesis → Thesis → Set
  (Pos x) ≡T (Pos y) = (Thesis'.pos x) ≡ (Thesis'.pos y)
  (Neg x) ≡T (Neg y) = (Thesis'.neg x) ≡ (Thesis'.neg y)
  (Th x)  ≡T (Th y)  = x ≡ y
  _ ≡T _ = ⊥
  

-- decidable equality
_≟T_ : Decidable _≡T_
x' ≟T y' with x' | y'
... | Pos x | Pos y = (Thesis'.pos x) S.≟ (Thesis'.pos y)
... | Neg x | Neg y = (Thesis'.neg x) S.≟ (Thesis'.neg y)
... | Th x  | Th y  = x S.≟ y
... | Pos _ | Neg _ = no id 
... | Pos _ | Th  _ = no id
... | Neg _ | Pos _ = no id
... | Neg _ | Th  _ = no id
... | Th  _ | Pos _ = no id
... | Th  _ | Neg _ = no id


instance
  TEq : BEq Thesis
  _===_ {{TEq}} x y = x =T y

-- Statement consists of Thesis and a particular text this thesis is stated in.
record Statement : Set where
  constructor st
  field
    sttext : Maybe String  -- the statement text
    thesis : Thesis        -- it's meaning (proposition)

-- bool equality
_=S_ : Statement → Statement → Bool
(st _ x) =S (st _ y) = x =T y

infix 4 _≟S_

private
  _≡S_ : Statement → Statement → Set
  x ≡S y = (Statement.thesis x) ≡T (Statement.thesis y)

_≟S_ : Decidable _≡S_
x ≟S y = (Statement.thesis x) ≟T (Statement.thesis y)


instance
  SEq : BEq Statement
  _===_ {{SEq}} x y = x =S y


docSection : ℕ → String → Doc
docSection n s = line <> text (s +++ "  ")
                 <> text (S.replicate (0 ℕ.⊔ ((n ∸ 2) ∸ S.length s)) '=')



-- float arithmetics

infix 5 _[<]_ _[≤]_ _[=]_
infix 6 _[+]_ _[-]_ 
infix 7 _[*]_

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
