module ShowDAG where

open import Data.Bool
open import Data.Empty
open import Data.Fin as Fin
  using (Fin; Fin′; zero; suc; #_; toℕ; _≟_) 
open import Data.Float
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat as Nat using (suc; ℕ)
open import Data.Nat.Show renaming (show to ℕshow)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String renaming (_++_ to _+++_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import ArgPrelude 
open import AIF
open import LabelAlgebras
open import ArgSchemes

open import DAG Pref


instance
  shLabel : ShowClass (Maybe FUnit)
  sh {{shLabel}} pre fu = pre +++ showlabel fu
    where
    showlabel : Maybe FUnit → String
    showlabel nothing = "NOTHING"
    showlabel (just (mkFUnit x _ _)) = Data.Float.show x

  shNode : ShowClass (LNode)
  sh {{shNode}} pre nd = showNode pre nd
    where
    showNode' : String → Node' → String
    showNode' pre (In (mkI s)) = sh pre s
    showNode' pre (Sn (SR (mkRA p c))) = sh "" c 
    showNode' pre (Sn (SC (mkCA c1 c2))) = pre +++ sh "CONFLICT1: " c1
      +++ sh "CONFLICT2: " c2
    showNode' pre (Sn (SP (mkPA p1 p2))) = pre +++ sh "PREF1: " p1
      +++ sh "PREF2: " p2

    showNode : String → LNode → String
    showNode pre (Ln n v) = pre +++ showNode' pre n +++ sh " ---> " v

  shSucs : ∀ {n} → ShowClass (List (Role × Fin n))
  sh {{shSucs}} pre l = showSucs pre l
    where
    showSucs : ∀ {n} → String → List (Role × Fin n) → String
    showSucs _ [] = ""
    showSucs pre (x ∷ xs) = pre +++ sh ":" (proj₁ x) +++ ": "
      +++ (sh "" (toℕ (proj₂ x)))
      +++ "\n" +++ showSucs pre xs 

  shContext : ∀ {n} → ShowClass (AContext n)
  sh {{shContext}} pre c = showContext pre c
    where
    showContext : ∀ {n} → String → AContext n → String
    showContext pre (context nd sucs) = pre +++ sh pre nd
      +++ "\n" +++ sh pre sucs

  shGraph : ∀ {n} → ShowClass (AGraph n)
  sh {{shGraph}} pre g = showAGraph pre g
    where
    showAGraph : ∀ {n} → String → AGraph n → String
    showAGraph {n} _ ∅ = ""
    showAGraph {suc n} pre (ctx & g) = sh ":: " n 
      +++ sh pre ctx +++ "\n" +++ showAGraph {n} pre g

  shFin : ∀ {n} → ShowClass (Fin n)
  sh {{shFin}} pre i = showFin pre i
    where
    showFin : ∀ {n} → String → Fin n → String
    showFin pre i = pre +++ ℕshow (toℕ i)

  shFinList : ∀ {n} → ShowClass (List (Fin n))
  sh {{shFinList}} pre l = showFinList pre l
    where
    showFinList : ∀ {n} → String → List (Fin n) → String
    showFinList pre [] = pre
    showFinList pre (x ∷ xs) = pre +++ (ℕshow (toℕ x)) +++ showFinList pre xs

  shFinNodeList : ∀ {n} → ShowClass (List (Fin n × LNode))
  sh {{shFinNodeList}} pre l = showFinNodeList pre l
    where
    showFinNodeList : ∀ {n} → String → List (Fin n × LNode) → String
    showFinNodeList pre [] = pre
    showFinNodeList pre (x ∷ xs) = pre +++ (ℕshow (toℕ (proj₁ x)))
      +++ " : " +++ sh "" (proj₂ x) +++ showFinNodeList pre xs
