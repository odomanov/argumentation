-- Examples: Direct Acyclic Graph
-- Example from Pereira et al. Changing One's Mind...

module ExABC where

open import Data.Fin as Fin
  using (Fin; Fin′; zero; suc; #_; toℕ; _≟_)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat
open import Data.Product using (_,_)
open import Data.String as S renaming (_++_ to _+++_)
open import Data.Vec as V using (Vec) renaming ([] to []v; _∷_ to _∷v_)

open import ArgPrelude 
open import AIF
open import LabelAlgebras
open import ArgSchemes

-- la = Pref
-- la = Łuk
la = Product
import DAG; module DAGla = DAG la; open DAGla

T1 = mkFrag "St1"
T2 = mkFrag "St2"
T3 = mkFrag "St3"

St1  = record { sttext = just T1; stprop = mkProp (Fragment.ftext T1)}
St2  = record { sttext = just T2; stprop = mkProp (Fragment.ftext T2)}
St3  = record { sttext = just T3; stprop = mkProp (Fragment.ftext T3)}

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

CA→C : ALNode
CA→C = Ln (Lnc record {Conflicting = conflicting; Conflicted = conflicted})
          (just (V 1.0 {refl} {refl}))



G : AGraph _
G =
     context CC→A ((conflicted , # 4) ∷ (conflicting , # 2) ∷ []) &
     context CB→C ((conflicted , # 1) ∷ (conflicting , # 2) ∷ []) &
     context CA→B ((conflicted , # 1) ∷ (conflicting , # 2) ∷ []) &
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

_ : NConflicts G (# 3) ≡ (# 1 , # 4) ∷ []
_ = refl

_ : NConflicts G (# 4) ≡ (# 2 , # 5) ∷ []
_ = refl

_ : NConflicts G (# 5) ≡ (# 0 , # 3) ∷ []
_ = refl



G0 = steps 0 G
G1 = steps 1 G
G2 = steps 2 G
G3 = steps 3 G
G4 = steps 4 G
G5 = steps 5 G
G6 = steps 6 G
G7 = steps 7 G
G10 = steps 10 G
G100 = steps 100 G
G200 = steps 200 G


G' : AGraph _
G' = context CA→C ((conflicted , # 3) ∷ (conflicting , # 5) ∷ []) & G

G'0 = steps 0 G'
G'1 = steps 1 G'
G'2 = steps 2 G'
G'3 = steps 3 G'
G'4 = steps 4 G'
G'5 = steps 5 G'
G'6 = steps 6 G'
G'7 = steps 7 G'
G'10 = steps 10 G'
G'100 = steps 100 G'
G'200 = steps 200 G'




------------------------------------------------------------------------

open import ShowDAG la

open import IO

w = 110
ws = 50 -- "section" title width

printABC : ℕ → String → AGraph 6 → (AGraph 6 → Fin 6 → MC) → String
printABC n s g f = "\n" +++ (spaces (0 ⊔ (n ∸ S.length s))) +++ s +++ ": "
           +++ " A = " +++ pprint w (f g (# 5))
           +++ " B = " +++ pprint w (f g (# 4))
           +++ " C = " +++ pprint w (f g (# 3))
printABC' : ℕ → String → AGraph 7 → (AGraph 7 → Fin 7 → MC) → String
printABC' n s g f = "\n" +++ (spaces (0 ⊔ (n ∸ S.length s))) +++ s +++ ": "
           +++ " A = " +++ pprint w (f g (# 6))
           +++ " B = " +++ pprint w (f g (# 5))
           +++ " C = " +++ pprint w (f g (# 4))

main = run (putStrLn stringToPrint)
  where
  wh = 10
  stringToPrint = S.replicate ws '-'
    -- +++ printABC wh "G orig" G val←i
    -- +++ printABC wh "G computed" G val
    +++ printABC wh "step 0" G0 val←i
    +++ printABC wh "step 1" G1 val←i
    +++ printABC wh "step 2" G2 val←i
    +++ printABC wh "step 3" G3 val←i
    +++ printABC wh "step 4" G4 val←i
    +++ printABC wh "step 5" G5 val←i
    +++ printABC wh "step 6" G6 val←i
    +++ printABC wh "step 7" G7 val←i
    +++ printABC wh "step 10" G10 val←i
    +++ printABC wh "step 100" G100 val←i
    +++ printABC wh "step 200" G200 val←i

    +++ "\n\nContradiction degree:  step0 = "
    +++ pprint w ((val←i G0 (# 3) ⟪⨂⟫ val←i G0 (# 4))
      ⟪⨁⟫⁺ (val←i G0 (# 4) ⟪⨂⟫ val←i G0 (# 5))
      ⟪⨁⟫⁺ (val←i G0 (# 5) ⟪⨂⟫ val←i G0 (# 3)))
    +++ " step200 = "
    +++ pprint w ((val←i G200 (# 3) ⟪⨂⟫ val←i G200 (# 4))
      ⟪⨁⟫⁺ (val←i G200 (# 4) ⟪⨂⟫ val←i G200 (# 5))
      ⟪⨁⟫⁺ (val←i G200 (# 5) ⟪⨂⟫ val←i G200 (# 3)))

    +++ "\nCorrectness: "
    +++ "  step0 = " +++ pprint w (Correctness G G0)
    +++ "  step1 = " +++ pprint w (Correctness G G1)
    +++ "  step2 = " +++ pprint w (Correctness G G2)
    +++ "  step3 = " +++ pprint w (Correctness G G3)
    +++ "\n             "
    +++ " step10 = " +++ pprint w (Correctness G G10)
    +++ "step100 = " +++ pprint w (Correctness G G100)
    +++ "step200 = " +++ pprint w (Correctness G G200)
    
    -- +++ printABC 17 "foldConflicts:G "  G foldConflicts
    -- +++ printABC 17 "foldConflicts:G5"  G5 foldConflicts
    -- +++ printABC 17 "-foldConflicts:G5" G5 ¬foldConflicts
    -- +++ printABC 17 "val+conflicts:G5"  G5 (val+conflicts G0)
    -- +++ printABC 17 "iterationVal:G5"   G5 (iterationVal G0)

    -- +++ (pprint 110 G)


    +++ "\n\n~~ with 1 more conflict ~~~~~"
    +++ printABC' wh "step 0" G'0 val←i
    +++ printABC' wh "step 1" G'1 val←i
    +++ printABC' wh "step 2" G'2 val←i
    +++ printABC' wh "step 3" G'3 val←i
    +++ printABC' wh "step 4" G'4 val←i
    +++ printABC' wh "step 5" G'5 val←i
    +++ printABC' wh "step 6" G'6 val←i
    +++ printABC' wh "step 7" G'7 val←i
    +++ printABC' wh "step 10" G'10 val←i
    +++ printABC' wh "step 100" G'100 val←i
    +++ printABC' wh "step 200" G'200 val←i

    +++ "\n\nContradiction degree:  step0 = "
    +++ pprint w ((val←i G'0 (# 4) ⟪⨂⟫ val←i G'0 (# 5))
      ⟪⨁⟫⁺ (val←i G'0 (# 5) ⟪⨂⟫ val←i G'0 (# 6))
      ⟪⨁⟫⁺ (val←i G'0 (# 6) ⟪⨂⟫ val←i G'0 (# 4))
      ⟪⨁⟫⁺ (val←i G'0 (# 4) ⟪⨂⟫ val←i G'0 (# 6)))
    +++ " step200 = "
    +++ pprint w ((val←i G'200 (# 4) ⟪⨂⟫ val←i G'200 (# 4))
      ⟪⨁⟫⁺ (val←i G'200 (# 5) ⟪⨂⟫ val←i G'200 (# 6))
      ⟪⨁⟫⁺ (val←i G'200 (# 6) ⟪⨂⟫ val←i G'200 (# 4))
      ⟪⨁⟫⁺ (val←i G'200 (# 4) ⟪⨂⟫ val←i G'200 (# 6)))

    +++ "\nCorrectness: "
    +++ "  step0 = " +++ pprint w (Correctness G' G'0)
    +++ "  step1 = " +++ pprint w (Correctness G' G'1)
    +++ "  step2 = " +++ pprint w (Correctness G' G'2)
    +++ "  step3 = " +++ pprint w (Correctness G' G'3)
    +++ "\n             "
    +++ " step10 = " +++ pprint w (Correctness G' G'10)
    +++ "step100 = " +++ pprint w (Correctness G' G'100)
    +++ "step200 = " +++ pprint w (Correctness G' G'200)
    
    -- +++ printABC' 17 "foldConflicts:G' "  G' foldConflicts
    -- +++ printABC' 17 "foldConflicts:G'5"  G'5 foldConflicts
    -- +++ printABC' 17 "-foldConflicts:G'5" G'5 ¬foldConflicts
    -- +++ printABC' 17 "val+conflicts:G'5"  G'5 (val+conflicts G'0)
    -- +++ printABC' 17 "iterationVal:G'5"   G'5 (iterationVal G'0)

    -- +++ (pprint 110 G')
