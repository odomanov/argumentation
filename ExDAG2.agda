-- Examples: Direct Acyclic Graph
-- Example from Pereira et al. Changing One's Mind...

module ExDAG2 where

open import Agda.Builtin.Float
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

la = Pref
-- la = Luk
open import DAG la

St1  = let t = "St1"
       in record { sttext = just t; stprop = mkProp t}
St2  = let t = "St2"
       in record { sttext = just t; stprop = mkProp t}
St3  = let t = "St3"
       in record { sttext = just t; stprop = mkProp t}

A : LNode
A = Ln (Lni St1) (just (V 1.0 {refl} {refl}))

B : LNode
B = Ln (Lni St2) (just (V 0.4 {refl} {refl}))

C : LNode
C = Ln (Lni St3) (just (V 0.2 {refl} {refl}))

CA→B : LNode
CA→B = Ln (Lnc record {Conflicting = conflicting; Conflicted = conflicted})
          (just (V 1.0 {refl} {refl}))

CB→C : LNode
CB→C = Ln (Lnc record {Conflicting = conflicting; Conflicted = conflicted})
          (just (V 1.0 {refl} {refl}))

CC→A : LNode
CC→A = Ln (Lnc record {Conflicting = conflicting; Conflicted = conflicted})
          (just (V 1.0 {refl} {refl}))



G : AGraph _
G =
     context CC→A ((conflicted , # 2) ∷ (conflicting , # 4) ∷ []) &
     context CB→C ((conflicted , # 2) ∷ (conflicting , # 1) ∷ []) &
     context CA→B ((conflicted , # 2) ∷ (conflicting , # 1) ∷ []) &
     context C [] &
     context B [] &
     context A [] &
     ∅


_ : nodes G ≡ (# 0 , CC→A) ∷ (# 1 , CB→C) ∷ (# 2 , CA→B)
             ∷ (# 3 , C)    ∷ (# 4 , B)    ∷ (# 5 , A)    ∷ []
_ = refl

_ : roots G ≡ (# 0 , CC→A) ∷ (# 1 , CB→C) ∷ (# 2 , CA→B) ∷ []
_ = refl

_ : roots¬CA G ≡ (# 3 , C) ∷ (# 4 , B)  ∷ (# 5 , A)  ∷ []
_ = refl

_ : NConflicts G (# 3) ≡ (# 4) ∷ []
_ = refl

_ : NConflicts G (# 4) ≡ (# 5) ∷ []
_ = refl

_ : NConflicts G (# 5) ≡ (# 3) ∷ []
_ = refl


G0 = compute G

_ : G0 ≡ steps 0 G
_ = refl

G1 = steps 1 G

G2 = steps 2 G

G3 = steps 3 G

G4 = steps 4 G

G5 = steps 5 G

G6 = steps 6 G

G7 = steps 7 G

G100 = steps 100 G

G200 = steps 200 G






------------------------------------------------------------------------

open import ShowDAG la

open import IO

w = 110
ws = 50 -- "section" title width

printABC : AGraph 6 → (AGraph 6 → Fin 6 → MC) → String
printABC g f = "\nA = " +++ pprint (f g (# 5))
           +++ "  B = " +++ pprint (f g (# 4))
           +++ "  C = " +++ pprint (f g (# 3))

main = run (putStrLn stringToPrint)
  where
  stringToPrint = replicate ws '-'
    +++ render (docSection ws "G orig")
    +++ printABC G val←Idx
    +++ render (docSection ws "G computed")
    +++ printABC G val
    +++ render (docSection ws "G0")
    +++ printABC G0 val←Idx
    +++ render (docSection ws "G1")
    +++ printABC G1 val←Idx
    +++ render (docSection ws "G2")
    +++ printABC G2 val←Idx
    +++ render (docSection ws "G3")
    +++ printABC G3 val←Idx
    +++ render (docSection ws "G4")
    +++ printABC G4 val←Idx
    +++ render (docSection ws "G5")
    +++ printABC G5 val←Idx
    +++ render (docSection ws "G6")
    +++ printABC G6 val←Idx
    +++ render (docSection ws "G7")
    +++ printABC G7 val←Idx
    +++ render (docSection ws "G100")
    +++ printABC G100 val←Idx
    +++ render (docSection ws "G200")
    +++ printABC G200 val←Idx

    -- +++ render (docSection ws "foldConflicts:G")
    -- +++ printABC G foldConflicts
    -- +++ render (docSection ws "foldConflicts:G5")
    -- +++ printABC G5 foldConflicts
    -- +++ render (docSection ws "¬foldConflicts:G5")
    -- +++ printABC G5 ¬foldConflicts
    -- +++ render (docSection ws "val+conflicts:G5")
    -- +++ printABC
