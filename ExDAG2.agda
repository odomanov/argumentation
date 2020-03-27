-- Examples: Direct Acyclic Graph
-- Example from Pereira et al. Changing One's Mind...

module ExDAG2 where

open import Data.Fin as Fin
  using (Fin; Fin′; zero; suc; #_; toℕ; _≟_)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe
open import Data.Product using (_,_)
open import Data.String renaming (_++_ to _+++_)
open import Data.Vec as V using (Vec) renaming ([] to []v; _∷_ to _∷v_)

open import ArgPrelude 
open import AIF
open import LabelAlgebras
open import ArgSchemes

la = Pref
-- la = Luk
import DAG; module DAGla = DAG la; open DAGla

St1  = let t = "St1"
       in record { sttext = just t; stprop = mkProp t}
St2  = let t = "St2"
       in record { sttext = just t; stprop = mkProp t}
St3  = let t = "St3"
       in record { sttext = just t; stprop = mkProp t}

A : ALNode
A = Ln (Lni St1) (just (V 1.0 {refl} {refl}))

B : ALNode
B = Ln (Lni St2) (just (V 0.4 {refl} {refl}))

C : ALNode
C = Ln (Lni St3) (just (V 0.2 {refl} {refl}))

CA→B : ALNode
CA→B = Ln (Lnc record {Conflicting = conflicting; Conflicted = conflicted})
          (just (V 1.0 {refl} {refl}))

CB→C : ALNode
CB→C = Ln (Lnc record {Conflicting = conflicting; Conflicted = conflicted})
          (just (V 1.0 {refl} {refl}))

CC→A : ALNode
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


_ : nodes G ≡ (# 0 , CC→A) ∷v (# 1 , CB→C) ∷v (# 2 , CA→B)
           ∷v (# 3 , C)    ∷v (# 4 , B)    ∷v (# 5 , A)    ∷v []v
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
printABC g f = "\nA = " +++ pprint w (f g (# 5))
           +++ "  B = " +++ pprint w (f g (# 4))
           +++ "  C = " +++ pprint w (f g (# 3))

main = run (putStrLn stringToPrint)
  where
  stringToPrint = "--------------------------------------------"
    +++ ppretty ws (docSection ws "\nG orig")
    +++ printABC G val←i
    +++ ppretty ws (docSection ws "G computed")
    +++ printABC G val
    +++ ppretty ws (docSection ws "G0")
    +++ printABC G0 val←i
    +++ ppretty ws (docSection ws "G1")
    +++ printABC G1 val←i
    +++ ppretty ws (docSection ws "G2")
    +++ printABC G2 val←i
    +++ ppretty ws (docSection ws "G3")
    +++ printABC G3 val←i
    +++ ppretty ws (docSection ws "G4")
    +++ printABC G4 val←i
    +++ ppretty ws (docSection ws "G5")
    +++ printABC G5 val←i
    +++ ppretty ws (docSection ws "G6")
    +++ printABC G6 val←i
    +++ ppretty ws (docSection ws "G7")
    +++ printABC G7 val←i
    +++ ppretty ws (docSection ws "G100")
    +++ printABC G100 val←i
    +++ ppretty ws (docSection ws "G200")
    +++ printABC G200 val←i

    -- +++ ppretty ws (docSection ws "foldConflicts:G")
    -- +++ printABC G foldConflicts
    -- +++ ppretty ws (docSection ws "foldConflicts:G5")
    -- +++ printABC G5 foldConflicts
    -- +++ ppretty ws (docSection ws "¬foldConflicts:G5")
    -- +++ printABC G5 ¬foldConflicts
    -- +++ ppretty ws (docSection ws "val+conflicts:G5")
    -- +++ printABC G5 (val+conflicts G0)
    -- +++ ppretty ws (docSection ws "iterationVal:G5")
    -- +++ printABC G5 (iterationVal G0)

    -- +++ (pprint 110 G)
