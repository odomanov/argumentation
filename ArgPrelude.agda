module ArgPrelude where

open import Agda.Builtin.Nat
open import Data.Bool using (Bool; true; false)
open import Data.Bool.Show using (show)
open import Data.Empty
open import Data.List
open import Data.Maybe
open import Data.Nat using (suc; ℕ)
open import Data.Nat.Show
open import Data.String as String using (String) renaming (_++_ to _+++_)
open import Data.Unit
open import Function using (id)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Level renaming (zero to lzero; suc to lsuc)

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
  field
    pos : String  -- positive form
    neg : String  -- negative form

data Thesis : Set where
  Pos : Thesis' → Thesis  -- тезис
  Neg : Thesis' → Thesis  -- отрицание тезиса
  Th  : String  → Thesis  -- если отрицание не определено / не требуется

-- bool equality
_=T_ : Thesis → Thesis → Bool
(Pos x) =T (Pos y) = (Thesis'.pos x) String.== (Thesis'.pos y)
(Neg x) =T (Neg y) = (Thesis'.pos x) String.== (Thesis'.pos y)
(Th x) =T (Th y) = x String.== y
_ =T _ = false



instance
  TEq : BEq Thesis
  _===_ {{TEq}} x y = x =T y

-- Statement consists of Thesis and a particular text this thesis is stated.
record Statement : Set where
  constructor st
  field
    text   : Maybe String  -- сам текст
    thesis : Thesis        -- его смысл / расшифровка (пропозиция)

-- bool equality
_=S_ : Statement → Statement → Bool
(st _ x) =S (st _ y) = x =T y


instance
  SEq : BEq Statement
  _===_ {{SEq}} x y = x =S y





-- Show handlers

record ShowClass {ℓ} (A : Set ℓ) : Set ℓ where
  field
    sh : String → A → String

open ShowClass {{...}} public

instance
  shBool : ShowClass Bool
  sh {{shBool}} pre b = pre +++ (Data.Bool.Show.show b)

  shString : ShowClass String
  sh {{shString}} pre s = pre +++ (String.show s)

  shNat : ShowClass Nat
  sh {{shNat}} pre n = pre +++ (Data.Nat.Show.show n)
