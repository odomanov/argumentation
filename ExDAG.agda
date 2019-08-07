-- Examples: Direct Acyclic Graph

module ExDAG where

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

import DAG
module DAGPref = DAG Pref 
open DAGPref 

module Example1 where

  St1  = let t = "St1"
         in record { text = just t; thesis = Th t}
  St2  = let t = "St2"
         in record { text = just t; thesis = Th t}
  Th3  = record { pos = "St3"; neg = "Not St3"}
  St3  = record { text = nothing; thesis = Pos Th3}
  ¬St3 = record { text = nothing; thesis = Neg Th3}
  St5  = let t = "St5"
         in record { text = just t; thesis = Th t}
  St7  = let t = "St7"
         in record { text = just t; thesis = Th t}
  
  N1 : LNode
  N1 = Ln (In record { Body = St1 }) (just (PV 0.2 {refl} {refl}))

  N2 : LNode
  N2 = Ln (In record { Body = St2 }) (just (PV 0.3 {refl} {refl}))

  N3 : LNode
  N3 = Ln (In record { Body = St3 }) nothing -- (just (PV 0.3 {refl} {refl}))

  ¬N3 : LNode
  ¬N3 = Ln (In record { Body = ¬St3 }) nothing -- (just (PV 0.3 {refl} {refl}))

  N4 : LNode
  N4 = Ln (Sn (SR A-от-эксперта)) (just (PV 0.1 {refl} {refl}))

  N5 : LNode
  N5 = Ln (In record { Body = St5 }) (just (PV 0.6 {refl} {refl}))

  N6 : LNode
  N6 = Ln (Sn (SR A-от-эксперта)) (just (PV 0.4 {refl} {refl}))

  N7 : LNode
  N7 = Ln (In record { Body = St7 }) (just (PV 0.9 {refl} {refl}))

  N8 : LNode
  N8 = Ln (Sn (SR A-ad-populum)) (just (PV 0.9 {refl} {refl}))

  CN1 : LNode
  CN1 = Ln (Sn (SC record {Conflicting = conflicting; Conflicted = conflicted}))
           (just (PV 0.8 {refl} {refl}))
  
  -- N1 ---+
  --        \
  --         N4 ---> N3
  --        /
  -- N2 ---+
  G1 : AGraph _
  G1 =
       context N3 ((поддержка , # 0) ∷ []) &
       context N4 ((эксперт , # 1) ∷ (говорит , # 0) ∷ []) &
       context N2 [] &
       context N1 [] &
       ∅
  
  _ : nodes G1 ≡ (# 0 , N3) ∷ (# 1 , N4) ∷ (# 2 , N2) ∷ (# 3 , N1) ∷ []
  _ = refl
  
  _ : edges G1 ≡ (# 0 , поддержка , # 0) ∷ (# 1 , эксперт , # 1) ∷ (# 1 , говорит , # 0) ∷ []
  _ = refl
  
  _ : G1 [ # 3 ] ≡ (context N1 [] & ∅)
  _ = refl
  
  _ : G1 [ # 2 ] ≡ (context N2 [] & context N1 [] & ∅)
  _ = refl
  
  _ : G1 [ # 1 ] ≡ ( context N4 ((эксперт , # 1) ∷ (говорит , # 0) ∷ []) &
                     context N2 [] & context N1 [] &
                     ∅
                   )
  _ = refl

  _ : roots G1 ≡ (_ , N3) ∷ []
  _ = refl
  
  _ : sucs G1 (# 1) ≡ (эксперт , # 1) ∷ (говорит , # 0) ∷ []
  _ = refl

  -- the same with implicit numbers
  _ : sucs G1 (# 1) ≡ (эксперт , _) ∷ (говорит , _) ∷ []
  _ = refl

  -- and even this way !!
  _ : sucs G1 (# 1) ≡ (_ , _) ∷ (_ , _) ∷ []
  _ = refl

  _ : sucs G1 (# 0) ≡ (поддержка , # 0) ∷ []
  _ = refl



  -- N2 ---- <N4> ---+
  --         /        \
  -- N1 ----+          N3
  --         \        /
  -- N5 ---- <N6> ---+
  G2 : AGraph _
  G2 =
       context N3 ((поддержка , # 0) ∷ (поддержка , # 2) ∷ []) &
       context N6 ((факт     , # 3) ∷ (объяснение , # 0) ∷ []) &
       context N5 [] &
       context N4 ((эксперт  , # 1) ∷ (говорит , # 0) ∷ []) &
       context N2 [] &
       context N1 [] &
       ∅

  -- part of G2, actually
  G3 : AGraph _
  G3 =
       context N4 ((эксперт  , # 1) ∷ (говорит , # 0) ∷ []) &
       context N2 [] &
       context N1 [] &
       ∅
  
  _ : nodes G2 ≡ (# 0 , N3) ∷ (# 1 , N6) ∷ (# 2 , N5) ∷ (# 3 , N4)
               ∷ (# 4 , N2) ∷ (# 5 , N1) ∷ []
  _ = refl
  
  _ : edges G2 ≡ (# 0 , поддержка , # 0) ∷ (# 0 , поддержка , # 2)
               ∷ (# 1 , факт , # 3) ∷ (# 1 , объяснение , # 0)
               ∷ (# 3 , эксперт , # 1) ∷ (# 3 , говорит , # 0) 
               ∷ []
  _ = refl
  
  
  _ : preds G2 (# 0) ≡ []
  _ = refl
  
  _ : preds G2 (# 3) ≡ (# 0 , поддержка) ∷ []
  _ = refl
  
  _ : preds G2 (# 5) ≡ (# 1 , факт) ∷ (# 3 , эксперт) ∷ []
  _ = refl


  _ : NArgs G2 (# 0) ≡ (поддержка , # 0) ∷ (поддержка , # 2) ∷ []
  _ = refl
  
  _ : NArgs G2 (# 4) ≡ []
  _ = refl
  
  _ : roots G2 ≡ (# 0 , N3) ∷ []
  _ = refl
  
  _ : G2 [ (# 0) ] ≡ G2
  _ = refl
  
  _ : G2 [ (# 0) > (# 0) ] ≡ G2 [ (# 1) ]
  _ = refl

  _ : theSame {5} (# 1) (# 0) (# 0) ≡ true
  _ = refl
  
  -- G3 is a part of G2
  _ : G2 [ (# 0) > (# 2) ] ≡ G3
  _ = refl
  
  -- не доказывается в общем виде
  -- ppp : ∀ {n} (g : AGraph (suc n)) (i : Fin (suc n)) → tail (g [ i ]) ≡ g [ (Fin.lower₁ (suc i) _) ]
  -- ppp {n} g i = ?
  
  -- хотя частные случаи доказываются:
  _ : tail (G2 [ (# 2) ]) ≡ G3
  _ = refl
  
  _ : G2 [ suc (# 2) ] ≡ G3
  _ = refl
  
  -- indexes
  
  _ : G2 ! (# 0) ≡ context N3 ((поддержка , # 0) ∷ (поддержка , # 2) ∷ [])
  _ = refl
  
  _ : G2 ! (# 1) ≡ context N6 ((факт     , # 3) ∷ (объяснение , # 0) ∷ [])
  _ = refl
  
  _ : G2 ![ (# 0) > (# 0) ] ≡ context N6 ((факт     , # 3) ∷ (объяснение , # 0) ∷ [])
  _ = refl
  
  _ : G2 ![ (# 1) > (# 2) ] ≡ context N2 []
  _ = refl
  



  -- N2 ---- <N4> ---+
  --         /        \
  -- N1 ----+          N3
  --         \        /|
  -- N5 ---- <N6> ---+ |
  --                   |
  -- N7 ---- <N8> -----+
  G4 : AGraph _
  G4 =
       context N3 ((атака , # 0) ∷ (поддержка , # 2) ∷ (поддержка , # 4) ∷ []) &
       context N8 ((все-признают , # 0) ∷ []) &
       context N7 [] &
       context N6 ((факт     , # 3) ∷ (объяснение , # 0) ∷ []) &
       context N5 [] &
       context N4 ((эксперт  , # 1) ∷ (говорит , # 0) ∷ []) &
       context N2 [] &
       context N1 [] &
       ∅

  _ : nodes G4 ≡ (# 0 , N3) ∷ (# 1 , N8) ∷ (# 2 , N7)
               ∷ (# 3 , N6) ∷ (# 4 , N5) ∷ (# 5 , N4)
               ∷ (# 6 , N2) ∷ (# 7 , N1) ∷ []
  _ = refl
  
  -- _ : edges G2 ≡ (# 0 , атака , # 0)
  --              ∷ (# 0 , поддержка , # 2) ∷ (# 0 , поддержка , # 4)
  --              ∷ (# 1 , все-признают , _)
  --              ∷ (# 3 , факт , # 3) ∷ (# 3 , объяснение , # 0)
  --              ∷ (# 5 , эксперт , # 1) ∷ (# 5 , говорит , # 0) 
  --              ∷ []
  -- _ = refl
  
  
  _ : preds G4 (# 0) ≡ []
  _ = refl
  
  _ : preds G4 (# 3) ≡ (# 0 , поддержка) ∷ []
  _ = refl
  
  _ : preds G4 (# 1) ≡ (# 0 , атака) ∷ []
  _ = refl
  
  _ : preds G4 (# 7) ≡ (# 3 , факт) ∷ (# 5 , эксперт) ∷ []
  _ = refl


  -- all inputs
  _ : NArgs G4 (# 0) ≡ (атака , # 0) ∷ (поддержка , # 2) ∷ (поддержка , # 4) ∷ []
  _ = refl

  -- only attacks
  _ : NArgs- G4 (# 0) ≡ (атака , # 0) ∷ []
  _ = refl

  -- only supports
  _ : NArgs+ G4 (# 0) ≡ (поддержка , # 2) ∷ (поддержка , # 4) ∷ []
  _ = refl


  _ : NArgs G4 (# 4) ≡ []
  _ = refl
  
  _ : NArgs+ G4 (# 4) ≡ []
  _ = refl
  
  _ : NArgs- G4 (# 4) ≡ []
  _ = refl
  
  _ : roots G4 ≡ (# 0 , N3) ∷ []
  _ = refl
  
  
  -- indexes
  
  _ : G4 ! (# 0) ≡ context N3 ((атака , _) ∷ (поддержка , _) ∷ (поддержка , _) ∷ [])
  _ = refl
  
  _ : G4 ! (# 3) ≡ context N6 ((факт     , _) ∷ (объяснение , _) ∷ [])
  _ = refl
  
  _ : G4 ![ (# 0) > (# 2) ] ≡ context N6 ((факт     , # 3) ∷ (объяснение , # 0) ∷ [])
  _ = refl
  
  _ : G4 ![ (# 3) > (# 2) ] ≡ context N2 []
  _ = refl
  

  -- Graph with conflicts  --------------------------------------------

  -- N2 ---- <N4> ---+
  --         /        \
  -- N1 ----+          N3
  --         \        /|
  -- N5 ---- <N6> ---+ CN1
  --                   |
  -- N7 ---- <N8> ----¬N3
  G5 : AGraph _
  G5 =
       context CN1 ((conflicted , # 0) ∷ (conflicting , # 3) ∷ []) &
       context ¬N3 ((поддержка , # 0) ∷ []) &
       context N8 ((все-признают , # 0) ∷ []) &
       context N7 [] &
       G2

  _ : nodes G5 ≡ (# 0 , CN1) ∷ (# 1 , ¬N3) ∷ (# 2 , N8) ∷ (# 3 , N7)
               ∷ (# 4 , N3)  ∷ (# 5 , N6)  ∷ (# 6 , N5) ∷ (# 7 , N4)
               ∷ (# 8 , N2)  ∷ (# 9 , N1)  ∷ []
  _ = refl

  _ : roots G5 ≡ (# 0 , CN1) ∷ []
  _ = refl
  
  _ : roots¬CA G5 ≡ (# 1 , ¬N3) ∷ (# 4 , N3) ∷ []
  _ = refl
  
  _ : theSame {10} (# 1) (# 0) (# 0) ≡ true
  _ = refl

  _ : theSame {10} (# 6) (# 2) (# 3) ≡ true
  _ = refl

  _ : realIdx {10} (# 0) (# 0) ≡ (# 1)
  _ = refl
  
  _ : realIdx {10} (# 2) (# 3) ≡ (# 6)
  _ = refl

  _ : realIdx {10} (# 0) (# 3) ≡ (# 4)
  _ = refl

  _ : realIdx {10} (# 4) (# 0) ≡ (# 5)
  _ = refl

  _ : c-ing G5 (# 0) ≡ just (# 3)
  _ = refl

  _ : c-ed G5 (# 0) ≡ just (# 0)
  _ = refl

  _ : c-ed G5 (# 1) ≡ nothing
  _ = refl

  _ : c-ed←CA G5 (# 0) (# 4) ≡ just (# 0)
  _ = refl
  
  _ : NConflicts G5 (# 0) ≡ [] 
  _ = refl

  _ : NConflicts G5 (# 1) ≡ []
  _ = refl

  _ : NConflicts G5 (# 2) ≡ [] 
  _ = refl

  _ : NConflicts G5 (# 4) ≡ (# 1) ∷ [] 
  _ = refl


  G50 = compute G5

  G51 = steps 1 G5

  G52 = steps 2 G5

  G53 = steps 3 G5

  G54 = steps 20 G5



-- From Pereira et al. Changing One's Mind...

module Example2 where

  St1  = let t = "St1"
         in record { text = just t; thesis = Th t}
  St2  = let t = "St2"
         in record { text = just t; thesis = Th t}
  St3  = let t = "St3"
         in record { text = just t; thesis = Th t}
  
  A : LNode
  A = Ln (In record { Body = St1 }) (just (PV 1.0 {refl} {refl}))

  B : LNode
  B = Ln (In record { Body = St2 }) (just (PV 0.4 {refl} {refl}))

  C : LNode
  C = Ln (In record { Body = St3 }) (just (PV 0.2 {refl} {refl}))

  CA→B : LNode
  CA→B = Ln (Sn (SC record {Conflicting = conflicting; Conflicted = conflicted}))
             (just (PV 1.0 {refl} {refl}))
  
  CB→C : LNode
  CB→C = Ln (Sn (SC record {Conflicting = conflicting; Conflicted = conflicted}))
             (just (PV 1.0 {refl} {refl}))
  
  CC→A : LNode
  CC→A = Ln (Sn (SC record {Conflicting = conflicting; Conflicted = conflicted}))
             (just (PV 1.0 {refl} {refl}))
  


  G5 : AGraph _
  G5 =
       context CC→A ((conflicted , # 2) ∷ (conflicting , # 4) ∷ []) &
       context CB→C ((conflicted , # 2) ∷ (conflicting , # 1) ∷ []) &
       context CA→B ((conflicted , # 2) ∷ (conflicting , # 1) ∷ []) &
       context C [] &
       context B [] &
       context A [] &
       ∅
  

  _ : nodes G5 ≡ (# 0 , CC→A) ∷ (# 1 , CB→C) ∷ (# 2 , CA→B)
               ∷ (# 3 , C)    ∷ (# 4 , B)    ∷ (# 5 , A)    ∷ []
  _ = refl

  _ : roots G5 ≡ (# 0 , CC→A) ∷ (# 1 , CB→C) ∷ (# 2 , CA→B) ∷ [] 
  _ = refl
  
  _ : roots¬CA G5 ≡ (# 3 , C) ∷ (# 4 , B)  ∷ (# 5 , A)  ∷ []
  _ = refl
  
  _ : NConflicts G5 (# 3) ≡ (# 4) ∷ []
  _ = refl

  _ : NConflicts G5 (# 4) ≡ (# 5) ∷ []
  _ = refl

  _ : NConflicts G5 (# 5) ≡ (# 3) ∷ []
  _ = refl


  G50 = compute G5

  _ : G50 ≡ steps 0 G5
  _ = refl
  
  G51 = steps 1 G5

  G52 = steps 2 G5

  G53 = steps 3 G5

  G54 = steps 4 G5

  G55 = steps 5 G5

  G56 = steps 6 G5

  G57 = steps 7 G5

  G5lim = steps 200 G5






------------------------------------------------------------------------

open import ShowDAG

open import IO

main = run (putStrLn stringToPrint)
  where
  ----- From Example1 --------------------------------------------
  -- open Example1 
  -- stringToPrint = "--------------------------------------------"
  --   -- +++ sh "\nN1 = " (val G2 (# 5))
  --   -- +++ sh "\nN2 = " (val G2 (# 4))
  --   -- +++ sh "\nN3 = " (val G2 (# 0))
  --   -- +++ sh "\nN4 = " (val G2 (# 3))
  --   -- +++ sh "\nN5 = " (val G2 (# 2))
  --   -- +++ sh "\nN6 = " (val G2 (# 1))
  --   -- +++ sh "\nN1+N2 = " (val←Ctx G2 (# 5) ⟪ _⊕_ Pref ⟫ val←Ctx G2 (# 4))
  --   -- +++ sh "\nN4+N6 = " (val←Ctx G2 (# 3) ⟪ _⊕_ Pref ⟫ val←Ctx G2 (# 1))
  --   -- +++ sh "\nN1+N5 = " (val←Ctx G2 (# 5) ⟪ _⊕_ Pref ⟫ val←Ctx G2 (# 2))
  --   -- +++ sh "\nN1.N2 = " (val←Ctx G2 (# 5) ⟪ _⊙_ Pref ⟫ val←Ctx G2 (# 4))
  --   -- +++ sh "\nN4.N6 = " (val←Ctx G2 (# 3) ⟪ _⊙_ Pref ⟫ val←Ctx G2 (# 1))
  --   -- +++ sh "\nN1.N5 = " (val←Ctx G2 (# 5) ⟪ _⊙_ Pref ⟫ val←Ctx G2 (# 2))
  --   -- +++ "\nG4  ======================="
  --   -- +++ sh "\nN1 = " (val G4 (# 7))
  --   -- +++ sh "\nN2 = " (val G4 (# 6))
  --   -- +++ sh "\nN3 = " (val G4 (# 0))
  --   -- +++ sh "\nN4 = " (val G4 (# 5))
  --   -- +++ sh "\nN5 = " (val G4 (# 4))
  --   -- +++ sh "\nN6 = " (val G4 (# 3))
  --   -- +++ sh "\nN7 = " (val G4 (# 2))
  --   -- +++ sh "\nN8 = " (val G4 (# 1))
  --   +++ "\nG5 orig ======================="
  --   +++ sh "\nN1  = " (val←Idx G5 (# 9))
  --   +++ sh "\nN2  = " (val←Idx G5 (# 8))
  --   +++ sh "\nN3  = " (val←Idx G5 (# 4))
  --   +++ sh "\nN4  = " (val←Idx G5 (# 7))
  --   +++ sh "\nN5  = " (val←Idx G5 (# 6))
  --   +++ sh "\nN6  = " (val←Idx G5 (# 5))
  --   +++ sh "\nN7  = " (val←Idx G5 (# 3))
  --   +++ sh "\nN8  = " (val←Idx G5 (# 2))
  --   +++ sh "\n-N3 = " (val←Idx G5 (# 1))
  --   +++ sh "\nCN1 = " (val←Idx G5 (# 0))
  --   +++ "\nG5 computed  ======================="
  --   +++ sh "\nN1  = " (val G5 (# 9))
  --   +++ sh "\nN2  = " (val G5 (# 8))
  --   +++ sh "\nN3  = " (val G5 (# 4))
  --   +++ sh "\nN4  = " (val G5 (# 7))
  --   +++ sh "\nN5  = " (val G5 (# 6))
  --   +++ sh "\nN6  = " (val G5 (# 5))
  --   +++ sh "\nN7  = " (val G5 (# 3))
  --   +++ sh "\nN8  = " (val G5 (# 2))
  --   +++ sh "\n-N3 = " (val G5 (# 1))
  --   +++ sh "\nCN1 = " (val G5 (# 0))
  --   -- +++ "\n============================\n"
  --   -- +++ sh "  " G2
  --   -- +++ "\nNConflicts 0: " +++ sh "" (NConflicts G5 (# 0))
  --   -- +++ "\nNConflicts 1: " +++ sh "" (NConflicts G5 (# 1))
  --   -- +++ "\nNConflicts 2: " +++ sh "" (NConflicts G5 (# 2))
  --   -- +++ "\nNConflicts 3: " +++ sh "" (NConflicts G5 (# 3))
  --   -- +++ "\nNConflicts 4: " +++ sh "" (NConflicts G5 (# 4))
  --   +++ "\nG50  ======================="
  --   +++ sh "\nN1  = " (val←Idx G50 (# 9))
  --   +++ sh "\nN2  = " (val←Idx G50 (# 8))
  --   +++ sh "\nN3  = " (val←Idx G50 (# 4))
  --   +++ sh "\nN4  = " (val←Idx G50 (# 7))
  --   +++ sh "\nN5  = " (val←Idx G50 (# 6))
  --   +++ sh "\nN6  = " (val←Idx G50 (# 5))
  --   +++ sh "\nN7  = " (val←Idx G50 (# 3))
  --   +++ sh "\nN8  = " (val←Idx G50 (# 2))
  --   +++ sh "\n-N3 = " (val←Idx G50 (# 1))
  --   +++ sh "\nCN1 = " (val←Idx G50 (# 0))
  --   +++ "\nG51  ======================="
  --   +++ sh "\nN1  = " (val←Idx G51 (# 9))
  --   +++ sh "\nN2  = " (val←Idx G51 (# 8))
  --   +++ sh "\nN3  = " (val←Idx G51 (# 4))
  --   +++ sh "\nN4  = " (val←Idx G51 (# 7))
  --   +++ sh "\nN5  = " (val←Idx G51 (# 6))
  --   +++ sh "\nN6  = " (val←Idx G51 (# 5))
  --   +++ sh "\nN7  = " (val←Idx G51 (# 3))
  --   +++ sh "\nN8  = " (val←Idx G51 (# 2))
  --   +++ sh "\n-N3 = " (val←Idx G51 (# 1))
  --   +++ sh "\nCN1 = " (val←Idx G51 (# 0))
  --   +++ "\nG52  ======================="
  --   +++ sh "\nN1  = " (val←Idx G52 (# 9))
  --   +++ sh "\nN2  = " (val←Idx G52 (# 8))
  --   +++ sh "\nN3  = " (val←Idx G52 (# 4))
  --   +++ sh "\nN4  = " (val←Idx G52 (# 7))
  --   +++ sh "\nN5  = " (val←Idx G52 (# 6))
  --   +++ sh "\nN6  = " (val←Idx G52 (# 5))
  --   +++ sh "\nN7  = " (val←Idx G52 (# 3))
  --   +++ sh "\nN8  = " (val←Idx G52 (# 2))
  --   +++ sh "\n-N3 = " (val←Idx G52 (# 1))
  --   +++ sh "\nCN1 = " (val←Idx G52 (# 0))
  --   +++ "\nG53  ======================="
  --   +++ sh "\nN1  = " (val←Idx G53 (# 9))
  --   +++ sh "\nN2  = " (val←Idx G53 (# 8))
  --   +++ sh "\nN3  = " (val←Idx G53 (# 4))
  --   +++ sh "\nN4  = " (val←Idx G53 (# 7))
  --   +++ sh "\nN5  = " (val←Idx G53 (# 6))
  --   +++ sh "\nN6  = " (val←Idx G53 (# 5))
  --   +++ sh "\nN7  = " (val←Idx G53 (# 3))
  --   +++ sh "\nN8  = " (val←Idx G53 (# 2))
  --   +++ sh "\n-N3 = " (val←Idx G53 (# 1))
  --   +++ sh "\nCN1 = " (val←Idx G53 (# 0))
  --   +++ "\nG54  ======================="
  --   +++ sh "\nN1  = " (val←Idx G54 (# 9))
  --   +++ sh "\nN2  = " (val←Idx G54 (# 8))
  --   +++ sh "\nN3  = " (val←Idx G54 (# 4))
  --   +++ sh "\nN4  = " (val←Idx G54 (# 7))
  --   +++ sh "\nN5  = " (val←Idx G54 (# 6))
  --   +++ sh "\nN6  = " (val←Idx G54 (# 5))
  --   +++ sh "\nN7  = " (val←Idx G54 (# 3))
  --   +++ sh "\nN8  = " (val←Idx G54 (# 2))
  --   +++ sh "\n-N3 = " (val←Idx G54 (# 1))
  --   +++ sh "\nCN1 = " (val←Idx G54 (# 0))
  --   -- +++ "\nG5repl0  ======================="
  --   -- +++ sh "\nN1 = " (val←Idx (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 7))
  --   -- +++ sh "\nN2 = " (val←Idx (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 6))
  --   -- +++ sh "\nN3 = " (val←Idx (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 0))
  --   -- +++ sh "\nN4 = " (val←Idx (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 5))
  --   -- +++ sh "\nN5 = " (val←Idx (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 4))
  --   -- +++ sh "\nN6 = " (val←Idx (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 3))
  --   -- +++ sh "\nN7 = " (val←Idx (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 2))
  --   -- +++ sh "\nN8 = " (val←Idx (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 1))
  --   -- +++ "\nG5repl2  ======================="
  --   -- +++ sh "\nN1 = " (val←Idx (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 7))
  --   -- +++ sh "\nN2 = " (val←Idx (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 6))
  --   -- +++ sh "\nN3 = " (val←Idx (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 0))
  --   -- +++ sh "\nN4 = " (val←Idx (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 5))
  --   -- +++ sh "\nN5 = " (val←Idx (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 4))
  --   -- +++ sh "\nN6 = " (val←Idx (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 3))
  --   -- +++ sh "\nN7 = " (val←Idx (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 2))
  --   -- +++ sh "\nN8 = " (val←Idx (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 1))
  --   -- +++ "\nG5repl7  ======================="
  --   -- +++ sh "\nN1 = " (val←Idx (replaceInGraph G5 (# 7) (just (LA⊤ Pref))) (# 7))
  --   -- +++ sh "\nN2 = " (val←Idx (replaceInGraph G5 (# 7) (just (LA⊤ Pref))) (# 6))
  --   -- +++ sh "\nN3 = " (val←Idx (replaceInGraph G5 (# 7) (just (LA⊤ Pref))) (# 0))
  --   -- +++ sh "\nN4 = " (val←Idx (replaceInGraph G5 (# 7) (just (LA⊤ Pref))) (# 5))
  --   -- +++ sh "\nN5 = " (val←Idx (replaceInGraph G5 (# 7) (just (LA⊤ Pref))) (# 4))
  --   -- +++ sh "\nN6 = " (val←Idx (replaceInGraph G5 (# 7) (just (LA⊤ Pref))) (# 3))
  --   -- +++ sh "\nN7 = " (val←Idx (replaceInGraph G5 (# 7) (just (LA⊤ Pref))) (# 2))
  --   -- +++ sh "\nN8 = " (val←Idx (replaceInGraph G5 (# 7) (just (LA⊤ Pref))) (# 1))
  --   +++ sh "\nfoldConflicts0: " (foldConflicts G5 (# 0))
  --   +++ sh "\nfoldConflicts1: " (foldConflicts G5 (# 1))
  --   +++ sh "\nfoldConflicts2: " (foldConflicts G5 (# 2))
  --   +++ sh "\nfoldConflicts3: " (foldConflicts G5 (# 3))
  --   +++ sh "\nfoldConflicts4: " (foldConflicts G5 (# 4))
  --   -- +++ "\nroots: " +++ sh "" (roots¬CA G5)
  --   -- +++ "\nNArgs0: " +++ sh "  " (NArgs G5 (# 0))
  --   -- +++ "\nNArgs1: " +++ sh "  " (NArgs G5 (# 1))
  --   -- +++ "\nNArgs4: " +++ sh "  " (NArgs G5 (# 4))

  ----- From Example2 --------------------------------------------
  open Example2
  stringToPrint = "--------------------------------------------"
    +++ "\nG5 orig ======================="
    +++ sh "\nA = " (val←Idx G5 (# 5))
    +++ sh "\nB = " (val←Idx G5 (# 4))
    +++ sh "\nC = " (val←Idx G5 (# 3))
    +++ "\nG5 computed  ======================="
    +++ sh "\nA = " (val G5 (# 5))
    +++ sh "\nB = " (val G5 (# 4))
    +++ sh "\nC = " (val G5 (# 3))
    +++ "\nG50 ======================="
    +++ sh "\nA = " (val←Idx G50 (# 5))
    +++ sh "\nB = " (val←Idx G50 (# 4))
    +++ sh "\nC = " (val←Idx G50 (# 3))
    +++ "\nG51 ======================="
    +++ sh "\nA = " (val←Idx G51 (# 5))
    +++ sh "\nB = " (val←Idx G51 (# 4))
    +++ sh "\nC = " (val←Idx G51 (# 3))
    +++ "\nG52 ======================="
    +++ sh "\nA = " (val←Idx G52 (# 5))
    +++ sh "\nB = " (val←Idx G52 (# 4))
    +++ sh "\nC = " (val←Idx G52 (# 3))
    +++ "\nG53 ======================="
    +++ sh "\nA = " (val←Idx G53 (# 5))
    +++ sh "\nB = " (val←Idx G53 (# 4))
    +++ sh "\nC = " (val←Idx G53 (# 3))
    +++ "\nG54 ======================="
    +++ sh "\nA = " (val←Idx G54 (# 5))
    +++ sh "\nB = " (val←Idx G54 (# 4))
    +++ sh "\nC = " (val←Idx G54 (# 3))
    +++ "\nG55 ======================="
    +++ sh "\nA = " (val←Idx G55 (# 5))
    +++ sh "\nB = " (val←Idx G55 (# 4))
    +++ sh "\nC = " (val←Idx G55 (# 3))
    +++ "\nG56 ======================="
    +++ sh "\nA = " (val←Idx G56 (# 5))
    +++ sh "\nB = " (val←Idx G56 (# 4))
    +++ sh "\nC = " (val←Idx G56 (# 3))
    +++ "\nG57 ======================="
    +++ sh "\nA = " (val←Idx G57 (# 5))
    +++ sh "\nB = " (val←Idx G57 (# 4))
    +++ sh "\nC = " (val←Idx G57 (# 3))
    +++ "\nG5lim ======================="
    +++ sh "\nA = " (val←Idx G5lim (# 5))
    +++ sh "\nB = " (val←Idx G5lim (# 4))
    +++ sh "\nC = " (val←Idx G5lim (# 3))
    -- +++ sh "\nfoldConflicts:G5:A: " (foldConflicts G5 (# 5))
    -- +++ sh "\nfoldConflicts:G5:B: " (foldConflicts G5 (# 4))
    -- +++ sh "\nfoldConflicts:G5:C: " (foldConflicts G5 (# 3))
    +++ sh "\nfoldConflicts:G55:A: " (foldConflicts G55 (# 5)) 
    +++ sh "\nfoldConflicts:G55:B: " (foldConflicts G55 (# 4)) 
    +++ sh "\nfoldConflicts:G55:C: " (foldConflicts G55 (# 3)) 
    +++ sh "\n-foldConflicts:G55:A: " (¬foldConflicts G55 (# 5)) 
    +++ sh "\n-foldConflicts:G55:B: " (¬foldConflicts G55 (# 4)) 
    +++ sh "\n-foldConflicts:G55:C: " (¬foldConflicts G55 (# 3)) 
    +++ sh "\nval+conflicts:G55:A: " (val+conflicts G50 G55 (# 5)) 
    +++ sh "\nval+conflicts:G55:B: " (val+conflicts G50 G55 (# 4)) 
    +++ sh "\nval+conflicts:G55:C: " (val+conflicts G50 G55 (# 3)) 
    +++ sh "\niterationVal:G55:A: " (iterationVal G50 G55 (# 5)) 
    +++ sh "\niterationVal:G55:B: " (iterationVal G50 G55 (# 4)) 
    +++ sh "\niterationVal:G55:C: " (iterationVal G50 G55 (# 3)) 


                              
