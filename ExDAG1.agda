-- Examples: Direct Acyclic Graph

module ExDAG1 where

open import Agda.Builtin.Float
open import Data.Bool
open import Data.Char renaming (Char to BChar)
open import Data.Empty
open import Data.Fin as Fin
  using (Fin; Fin′; zero; suc; #_; toℕ; _≟_)
open import Data.Float
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat as Nat using (suc; ℕ; _∸_)
open import Data.Nat.Show renaming (show to ℕshow)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String as S renaming (_++_ to _+++_)
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


St1  = let t = "St1"
       in record { sttext = just t; thesis = Th t}
St2  = let t = "St2"
       in record { sttext = just t; thesis = Th t}
Th3  = record { pos = "St3"; neg = "Not St3"}
St3  = record { sttext = nothing; thesis = Pos Th3}
¬St3 = record { sttext = nothing; thesis = Neg Th3}
St5  = let t = "St5"
       in record { sttext = just t; thesis = Th t}
St7  = let t = "St7"
       in record { sttext = just t; thesis = Th t}

N1 : LNode
N1 = Ln (In record { Body = St1 }) (just (PV 0.7 {refl} {refl}))

N2 : LNode
N2 = Ln (In record { Body = St2 }) (just (PV 1.0 {refl} {refl}))

N3 : LNode
N3 = Ln (In record { Body = St3 }) nothing -- (just (PV 1.3 {refl} {refl}))

¬N3 : LNode
¬N3 = Ln (In record { Body = ¬St3 }) nothing -- (just (PV 0.3 {refl} {refl}))

N4 : LNode
N4 = Ln (Sn (SR A-от-эксперта)) (just (PV 0.5 {refl} {refl}))

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


G10 = compute G1

G11 = steps 1 G1

G12 = steps 2 G1

G13 = steps 3 G1

G14 = steps 4 G1

G1lim = steps 100 G1




-- N2 ---- <N4> ----
--         /        \
-- N1 ----⟨          N3
--         \        /
-- N5 ---- <N6> ----
G2 : AGraph _
G2 =
     context N3 ((атака , # 0) ∷ (поддержка , # 2) ∷ []) &
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

_ : edges G2 ≡ (# 0 , атака , # 0) ∷ (# 0 , поддержка , # 2)
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


_ : NArgs G2 (# 0) ≡ (атака , # 0) ∷ (поддержка , # 2) ∷ []
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

_ : G2 ! (# 0) ≡ context N3 ((атака , # 0) ∷ (поддержка , # 2) ∷ [])
_ = refl

_ : G2 ! (# 1) ≡ context N6 ((факт     , # 3) ∷ (объяснение , # 0) ∷ [])
_ = refl

_ : G2 ![ (# 0) > (# 0) ] ≡ context N6 ((факт     , # 3) ∷ (объяснение , # 0) ∷ [])
_ = refl

_ : G2 ![ (# 1) > (# 2) ] ≡ context N2 []
_ = refl


G20 = compute G2

G21 = steps 1 G2

G22 = steps 2 G2

G23 = steps 3 G2

G24 = steps 4 G2

G2lim = steps 100 G2



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

_ : edges G4 ≡ (# 0 , атака , # 0)
             ∷ (# 0 , поддержка , # 2) ∷ (# 0 , поддержка , # 4)
             ∷ (# 1 , все-признают , _)
             ∷ (# 3 , факт , # 3) ∷ (# 3 , объяснение , # 0)
             ∷ (# 5 , эксперт , # 1) ∷ (# 5 , говорит , # 0)
             ∷ []
_ = refl


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


G40 = compute G4

G41 = steps 1 G4

G4lim = steps 100 G4




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






------------------------------------------------------------------------

open import ShowDAG

open import IO

w = 110
ws = 50 -- "section" title width

printG1 : AGraph 4 → String
printG1 g = "\nN1  = " +++ pprint w (val←Idx g (# 3))
        +++ "  N2  = " +++ pprint w (val←Idx g (# 2))
        +++ "\nN3  = " +++ pprint w (val←Idx g (# 0))
        +++ "  N4  = " +++ pprint w (val←Idx g (# 1))
printG2 : AGraph 6 → String
printG2 g = "\nN1  = " +++ pprint w (val←Idx g (# 5))
        +++ "  N2  = " +++ pprint w (val←Idx g (# 4))
        +++ "\nN3  = " +++ pprint w (val←Idx g (# 0))
        +++ "  N4  = " +++ pprint w (val←Idx g (# 3))
        +++ "\nN5  = " +++ pprint w (val←Idx g (# 2))
        +++ "  N6  = " +++ pprint w (val←Idx g (# 1))
printG4 : AGraph 8 → String
printG4 g = "\nN1 = " +++ pprint w (val←Idx G4 (# 7))
        +++ "  N2 = " +++ pprint w (val←Idx G4 (# 6))
        +++ "\nN3 = " +++ pprint w (val←Idx G4 (# 0))
        +++ "  N4 = " +++ pprint w (val←Idx G4 (# 5))
        +++ "\nN5 = " +++ pprint w (val←Idx G4 (# 4))
        +++ "  N6 = " +++ pprint w (val←Idx G4 (# 3))
        +++ "\nN7 = " +++ pprint w (val←Idx G4 (# 2))
        +++ "  N8 = " +++ pprint w (val←Idx G4 (# 1))

-- docFilled : ℕ → Doc → BChar → Doc
-- docFilled n d filler = d <> text ((S.replicate (n ∸ S.length ss)) filler)
--   where
--   ss = layout (renderPretty 1.0 n d)
  
main = run (putStrLn stringToPrint)
  where
  stringToPrint = S.replicate ws '-'
    -- +++ ppretty ws (docFilled ws line '-')
    -- +++ ppretty ws (docFilled ws (text "\nG1 orig  ") '=')
    -- +++ ppretty ws (docSection ws "G1 orig")
    -- +++ printG1 G1
    -- +++ ppretty ws (docSection ws "G1 computed")
    -- +++ "\nN1  = " +++ pprint w (val G1 (# 3))
    -- +++ "  N2  = " +++ pprint w (val G1 (# 2))
    -- +++ "\nN3  = " +++ pprint w (val G1 (# 0))
    -- +++ "  N4  = " +++ pprint w (val G1 (# 1))
    -- +++ ppretty ws (docSection ws "G10")
    -- +++ printG1 G10
    -- +++ ppretty ws (docSection ws "G11")
    -- +++ printG1 G11
    -- +++ ppretty ws (docSection ws "G12")
    -- +++ printG1 G12
    -- +++ ppretty ws (docSection ws "G13")
    -- +++ printG1 G13
    -- +++ ppretty ws (docSection ws "G14")
    -- +++ printG1 G14
    -- +++ ppretty ws (docSection ws "G1lim")
    -- +++ printG1 G1lim

    +++ ppretty ws (docSection ws "G2 orig")
    +++ printG2 G2
    +++ ppretty ws (docSection ws "G2 computed")
    +++ "\nN1  = " +++ pprint w (val G2 (# 5))
    +++ "  N2  = " +++ pprint w (val G2 (# 4))
    +++ "\nN3  = " +++ pprint w (val G2 (# 0))
    +++ "  N4  = " +++ pprint w (val G2 (# 3))
    +++ "\nN5  = " +++ pprint w (val G2 (# 2))
    +++ "  N6  = " +++ pprint w (val G2 (# 1))
    +++ ppretty ws (docSection ws "G20")
    +++ printG2 G20
    -- +++ ppretty ws (docSection ws "G21")
    -- +++ printG2 G21
    -- +++ ppretty ws (docSection ws "G22")
    -- +++ printG2 G22
    -- +++ ppretty ws (docSection ws "G23")
    -- +++ printG2 G23
    -- +++ ppretty ws (docSection ws "G24")
    -- +++ printG2 G24
    +++ ppretty ws (docSection ws "G2lim")
    +++ printG2 G2lim

    -- +++ pprint 110 G2
    
    -- +++ ppretty ws (docSection ws "G4 orig")
    -- +++ printG4 G4
    -- +++ ppretty ws (docSection ws "G4 computed")
    -- +++ "\nN1 = " +++ pprint w (val G4 (# 7))
    -- +++ "  N2 = " +++ pprint w (val G4 (# 6))
    -- +++ "\nN3 = " +++ pprint w (val G4 (# 0))
    -- +++ "  N4 = " +++ pprint w (val G4 (# 5))
    -- +++ "\nN5 = " +++ pprint w (val G4 (# 4))
    -- +++ "  N6 = " +++ pprint w (val G4 (# 3))
    -- +++ "\nN7 = " +++ pprint w (val G4 (# 2))
    -- +++ "  N8 = " +++ pprint w (val G4 (# 1))
    -- +++ ppretty ws (docSection ws "G40")
    -- +++ printG4 G40
    -- +++ ppretty ws (docSection ws "G41")
    -- +++ printG4 G41
    -- +++ ppretty ws (docSection ws "G4lim")
    -- +++ printG4 G4lim

    -- +++ "\nN1 = " +++ pprint w (val G2 (# 5))
    -- +++ "\nN2 = " +++ pprint w (val G2 (# 4))
    -- +++ "\nN3 = " +++ pprint w (val G2 (# 0))
    -- +++ "\nN4 = " +++ pprint w (val G2 (# 3))
    -- +++ "\nN5 = " +++ pprint w (val G2 (# 2))
    -- +++ "\nN6 = " +++ pprint w (val G2 (# 1))
    -- +++ "\nN1+N2 = " +++ pprint w (val←Ctx G2 (# 5) ⟪ _⊕_ Pref ⟫ val←Ctx G2 (# 4))
    -- +++ "\nN4+N6 = " +++ pprint w (val←Ctx G2 (# 3) ⟪ _⊕_ Pref ⟫ val←Ctx G2 (# 1))
    -- +++ "\nN1+N5 = " +++ pprint w (val←Ctx G2 (# 5) ⟪ _⊕_ Pref ⟫ val←Ctx G2 (# 2))
    -- +++ "\nN1.N2 = " +++ pprint w (val←Ctx G2 (# 5) ⟪ _⊙_ Pref ⟫ val←Ctx G2 (# 4))
    -- +++ "\nN4.N6 = " +++ pprint w (val←Ctx G2 (# 3) ⟪ _⊙_ Pref ⟫ val←Ctx G2 (# 1))
    -- +++ "\nN1.N5 = " +++ pprint w (val←Ctx G2 (# 5) ⟪ _⊙_ Pref ⟫ val←Ctx G2 (# 2))
    -- +++ "\nG4  ======================="
    -- +++ "\nN1 = " +++ pprint w (val G4 (# 7))
    -- +++ "\nN2 = " +++ pprint w (val G4 (# 6))
    -- +++ "\nN3 = " +++ pprint w (val G4 (# 0))
    -- +++ "\nN4 = " +++ pprint w (val G4 (# 5))
    -- +++ "\nN5 = " +++ pprint w (val G4 (# 4))
    -- +++ "\nN6 = " +++ pprint w (val G4 (# 3))
    -- +++ "\nN7 = " +++ pprint w (val G4 (# 2))
    -- +++ "\nN8 = " +++ pprint w (val G4 (# 1))
    -- +++ "\nG5 orig ======================="
    -- +++ "\nN1  = " +++ pprint w (val←Idx G5 (# 9))
    -- +++ "\nN2  = " +++ pprint w (val←Idx G5 (# 8))
    -- +++ "\nN3  = " +++ pprint w (val←Idx G5 (# 4))
    -- +++ "\nN4  = " +++ pprint w (val←Idx G5 (# 7))
    -- +++ "\nN5  = " +++ pprint w (val←Idx G5 (# 6))
    -- +++ "\nN6  = " +++ pprint w (val←Idx G5 (# 5))
    -- +++ "\nN7  = " +++ pprint w (val←Idx G5 (# 3))
    -- +++ "\nN8  = " +++ pprint w (val←Idx G5 (# 2))
    -- +++ "\n-N3 = " +++ pprint w (val←Idx G5 (# 1))
    -- +++ "\nCN1 = " +++ pprint w (val←Idx G5 (# 0))
    -- +++ "\nG5 computed  ======================="
    -- +++ "\nN1  = " +++ pprint w (val G5 (# 9))
    -- +++ "\nN2  = " +++ pprint w (val G5 (# 8))
    -- +++ "\nN3  = " +++ pprint w (val G5 (# 4))
    -- +++ "\nN4  = " +++ pprint w (val G5 (# 7))
    -- +++ "\nN5  = " +++ pprint w (val G5 (# 6))
    -- +++ "\nN6  = " +++ pprint w (val G5 (# 5))
    -- +++ "\nN7  = " +++ pprint w (val G5 (# 3))
    -- +++ "\nN8  = " +++ pprint w (val G5 (# 2))
    -- +++ "\n-N3 = " +++ pprint w (val G5 (# 1))
    -- +++ "\nCN1 = " +++ pprint w (val G5 (# 0))
    -- -- +++ "\n============================\n"
    -- -- +++ "  " +++ pprint w G2
    -- -- +++ "\nNConflicts 0: " +++ "" +++ pprint w (NConflicts G5 (# 0))
    -- -- +++ "\nNConflicts 1: " +++ "" +++ pprint w (NConflicts G5 (# 1))
    -- -- +++ "\nNConflicts 2: " +++ "" +++ pprint w (NConflicts G5 (# 2))
    -- -- +++ "\nNConflicts 3: " +++ "" +++ pprint w (NConflicts G5 (# 3))
    -- -- +++ "\nNConflicts 4: " +++ "" +++ pprint w (NConflicts G5 (# 4))
    -- +++ "\nG50  ======================="
    -- +++ "\nN1  = " +++ pprint w (val←Idx G50 (# 9))
    -- +++ "\nN2  = " +++ pprint w (val←Idx G50 (# 8))
    -- +++ "\nN3  = " +++ pprint w (val←Idx G50 (# 4))
    -- +++ "\nN4  = " +++ pprint w (val←Idx G50 (# 7))
    -- +++ "\nN5  = " +++ pprint w (val←Idx G50 (# 6))
    -- +++ "\nN6  = " +++ pprint w (val←Idx G50 (# 5))
    -- +++ "\nN7  = " +++ pprint w (val←Idx G50 (# 3))
    -- +++ "\nN8  = " +++ pprint w (val←Idx G50 (# 2))
    -- +++ "\n-N3 = " +++ pprint w (val←Idx G50 (# 1))
    -- +++ "\nCN1 = " +++ pprint w (val←Idx G50 (# 0))
    -- +++ "\nG51  ======================="
    -- +++ "\nN1  = " +++ pprint w (val←Idx G51 (# 9))
    -- +++ "\nN2  = " +++ pprint w (val←Idx G51 (# 8))
    -- +++ "\nN3  = " +++ pprint w (val←Idx G51 (# 4))
    -- +++ "\nN4  = " +++ pprint w (val←Idx G51 (# 7))
    -- +++ "\nN5  = " +++ pprint w (val←Idx G51 (# 6))
    -- +++ "\nN6  = " +++ pprint w (val←Idx G51 (# 5))
    -- +++ "\nN7  = " +++ pprint w (val←Idx G51 (# 3))
    -- +++ "\nN8  = " +++ pprint w (val←Idx G51 (# 2))
    -- +++ "\n-N3 = " +++ pprint w (val←Idx G51 (# 1))
    -- +++ "\nCN1 = " +++ pprint w (val←Idx G51 (# 0))
    -- +++ "\nG52  ======================="
    -- +++ "\nN1  = " +++ pprint w (val←Idx G52 (# 9))
    -- +++ "\nN2  = " +++ pprint w (val←Idx G52 (# 8))
    -- +++ "\nN3  = " +++ pprint w (val←Idx G52 (# 4))
    -- +++ "\nN4  = " +++ pprint w (val←Idx G52 (# 7))
    -- +++ "\nN5  = " +++ pprint w (val←Idx G52 (# 6))
    -- +++ "\nN6  = " +++ pprint w (val←Idx G52 (# 5))
    -- +++ "\nN7  = " +++ pprint w (val←Idx G52 (# 3))
    -- +++ "\nN8  = " +++ pprint w (val←Idx G52 (# 2))
    -- +++ "\n-N3 = " +++ pprint w (val←Idx G52 (# 1))
    -- +++ "\nCN1 = " +++ pprint w (val←Idx G52 (# 0))
    -- +++ "\nG53  ======================="
    -- +++ "\nN1  = " +++ pprint w (val←Idx G53 (# 9))
    -- +++ "\nN2  = " +++ pprint w (val←Idx G53 (# 8))
    -- +++ "\nN3  = " +++ pprint w (val←Idx G53 (# 4))
    -- +++ "\nN4  = " +++ pprint w (val←Idx G53 (# 7))
    -- +++ "\nN5  = " +++ pprint w (val←Idx G53 (# 6))
    -- +++ "\nN6  = " +++ pprint w (val←Idx G53 (# 5))
    -- +++ "\nN7  = " +++ pprint w (val←Idx G53 (# 3))
    -- +++ "\nN8  = " +++ pprint w (val←Idx G53 (# 2))
    -- +++ "\n-N3 = " +++ pprint w (val←Idx G53 (# 1))
    -- +++ "\nCN1 = " +++ pprint w (val←Idx G53 (# 0))
    -- +++ "\nG54  ======================="
    -- +++ "\nN1  = " +++ pprint w (val←Idx G54 (# 9))
    -- +++ "\nN2  = " +++ pprint w (val←Idx G54 (# 8))
    -- +++ "\nN3  = " +++ pprint w (val←Idx G54 (# 4))
    -- +++ "\nN4  = " +++ pprint w (val←Idx G54 (# 7))
    -- +++ "\nN5  = " +++ pprint w (val←Idx G54 (# 6))
    -- +++ "\nN6  = " +++ pprint w (val←Idx G54 (# 5))
    -- +++ "\nN7  = " +++ pprint w (val←Idx G54 (# 3))
    -- +++ "\nN8  = " +++ pprint w (val←Idx G54 (# 2))
    -- +++ "\n-N3 = " +++ pprint w (val←Idx G54 (# 1))
    -- +++ "\nCN1 = " +++ pprint w (val←Idx G54 (# 0))
    -- +++ "\nG5repl0  ======================="
    -- +++ "\nN1 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 7))
    -- +++ "\nN2 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 6))
    -- +++ "\nN3 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 0))
    -- +++ "\nN4 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 5))
    -- +++ "\nN5 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 4))
    -- +++ "\nN6 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 3))
    -- +++ "\nN7 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 2))
    -- +++ "\nN8 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 1))
    -- +++ "\nG5repl2  ======================="
    -- +++ "\nN1 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 7))
    -- +++ "\nN2 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 6))
    -- +++ "\nN3 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 0))
    -- +++ "\nN4 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 5))
    -- +++ "\nN5 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 4))
    -- +++ "\nN6 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 3))
    -- +++ "\nN7 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 2))
    -- +++ "\nN8 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 1))
    -- +++ "\nG5repl7  ======================="
    -- +++ "\nN1 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 7) (just (LA⊤ Pref))) (# 7))
    -- +++ "\nN2 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 7) (just (LA⊤ Pref))) (# 6))
    -- +++ "\nN3 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 7) (just (LA⊤ Pref))) (# 0))
    -- +++ "\nN4 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 7) (just (LA⊤ Pref))) (# 5))
    -- +++ "\nN5 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 7) (just (LA⊤ Pref))) (# 4))
    -- +++ "\nN6 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 7) (just (LA⊤ Pref))) (# 3))
    -- +++ "\nN7 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 7) (just (LA⊤ Pref))) (# 2))
    -- +++ "\nN8 = " +++ pprint w (val←Idx (replaceInGraph G5 (# 7) (just (LA⊤ Pref))) (# 1))
    -- +++ "\nfoldConflicts0: " +++ pprint w (foldConflicts G5 (# 0))
    -- +++ "\nfoldConflicts1: " +++ pprint w (foldConflicts G5 (# 1))
    -- +++ "\nfoldConflicts2: " +++ pprint w (foldConflicts G5 (# 2))
    -- +++ "\nfoldConflicts3: " +++ pprint w (foldConflicts G5 (# 3))
    -- +++ "\nfoldConflicts4: " +++ pprint w (foldConflicts G5 (# 4))
    -- +++ "\nroots: " +++ "" +++ pprint w (roots¬CA G5)
    -- +++ "\nNArgs0: " +++ "  " +++ pprint w (NArgs G5 (# 0))
    -- +++ "\nNArgs1: " +++ "  " +++ pprint w (NArgs G5 (# 1))
    -- +++ "\nNArgs4: " +++ "  " +++ pprint w (NArgs G5 (# 4))

    -- +++ (pprint 110 G5)
