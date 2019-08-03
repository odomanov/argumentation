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
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary

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
... | Pos x | Pos y = (Thesis'.pos x) String.≟ (Thesis'.pos y)
... | Neg x | Neg y = (Thesis'.neg x) String.≟ (Thesis'.neg y)
... | Th x  | Th y  = x String.≟ y
... | Pos x | Neg y = no id 
... | Pos x | Th y  = no id
... | Neg x | Pos y = no id
... | Neg x | Th y  = no id
... | Th x  | Pos y = no id
... | Th x  | Neg y = no id


instance
  TEq : BEq Thesis
  _===_ {{TEq}} x y = x =T y

-- Statement consists of Thesis and a particular text this thesis is stated in.
record Statement : Set where
  constructor st
  field
    text   : Maybe String  -- the text
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

  shThesis : ShowClass Thesis
  sh {{shThesis}} pre t = showThesis pre t
    where
    showThesis : String → Thesis → String
    showThesis pre (Pos t) = pre +++ "POS: " +++ Thesis'.pos t
    showThesis pre (Neg t) = pre +++ "NEG: " +++ Thesis'.neg t
    showThesis pre (Th s) = pre +++ s

  shStatement : ShowClass Statement
  sh {{shStatement}} pre s = showStatement pre s
    where 
    showStatement : String → Statement → String
    showStatement pre (st nothing th) = "\n"
      +++ pre +++ sh "" th 
    showStatement pre (st (just t) th) = "\n"
      +++ pre +++ sh "" th +++ "\n" 
      +++ pre +++ "(TEXT: " +++ t +++ ")" 
