-- Examples: Direct Acyclic Graph

module Ex1 where

open import Data.Bool
open import Data.Char renaming (Char to BChar)
open import Data.Empty
open import Data.Fin as Fin
  using (Fin; Fin′; zero; suc; #_; toℕ; _≟_)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat as ℕ using (suc; ℕ; _∸_)
open import Data.Nat.Show renaming (show to ℕshow)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String as S renaming (_++_ to _+++_)
open import Data.Vec as Vec using (Vec) renaming ([] to []v; _∷_ to _∷v_)
open import Data.Unit

open import ArgPrelude 
open import AIF
open import LabelAlgebras
open import ArgSchemes

-- la = Pref
la = Łuk
import DAG; module DAGla = DAG la; open DAGla

node : ∀ {n} → ANode
             → (v : Float) → {0.0 [≤] v ≡ true} → {v [≤] 1.0 ≡ true}
             → Sucs n
             → AContext n
node nd v {p0} {p1} sucs = context (Ln nd (just (V v {p0} {p1}))) sucs

node0 : ∀ {n} → ANode → Sucs n → AContext n
node0 nd sucs = context (Ln nd nothing) sucs

T1 = mkFrag "St1"
T2 = mkFrag "St2"
T3 = mkFrag "St3"
T5 = mkFrag "St5"
T7 = mkFrag "St7"

St1  = record { sttext = just T1; stprop = mkProp (Fragment.ftext T1)}
St2  = record { sttext = just T2; stprop = mkProp (Fragment.ftext T2)}
St3  = record { sttext = nothing; stprop = mkProp (Fragment.ftext T3)}
¬St3 = record { sttext = nothing; stprop = NOT (mkProp (Fragment.ftext T3))}
St5  = record { sttext = just T5; stprop = mkProp (Fragment.ftext T5)}
St7  = record { sttext = just T7; stprop = mkProp (Fragment.ftext T7)}

SC = record {Conflicting = conflicting; Conflicted = conflicted}

-- Statements
NS1  : ANode;  NS1 = Lni St1
NS2  : ANode;  NS2 = Lni St2
NS3  : ANode;  NS3 = Lni St3
¬NS3 : ANode; ¬NS3 = Lni ¬St3
NS5  : ANode;  NS5 = Lni St5
NS7  : ANode;  NS7 = Lni St7

-- Schemes
NA4 : ANode; NA4 = Lnr A-от-эксперта
NA6 : ANode; NA6 = Lnr A-абдукция
NA8 : ANode; NA8 = Lnr A-ad-populum
NC1 : ANode; NC1 = Lnc SC
NC2 : ANode; NC2 = Lnc SC



-- N1 ---+
--        \
--         N4 ---> N3
--        /
-- N2 ---+
G1 : AGraph _
G1 =
     node0 NS3 ((поддержка , # 0) ∷ []) &
     node NA4 0.5 {refl} {refl} ((эксперт , # 1) ∷ (говорит , # 0) ∷ []) & -- missed: область
     node NS2 1.0 {refl} {refl} [] &
     node NS1 0.7 {refl} {refl} [] &
     ∅

_ : nodes G1 ≡ (# 0 , (Ln NS3 _)) ∷v (# 1 , (Ln NA4 _)) ∷v (# 2 , (Ln NS2 _)) ∷v (# 3 , (Ln NS1 _)) ∷v []v
_ = refl

_ : edges G1 ≡ (# 0 , поддержка , # 0) ∷ (# 1 , эксперт , # 1) ∷ (# 1 , говорит , # 0) ∷ []
_ = refl

_ : G1 [ # 3 ] ≡ (node NS1 0.7 {refl} {refl} [] & ∅)
_ = refl

_ : G1 [ # 2 ] ≡ (node NS2 1.0 {refl} {refl} [] & node NS1 0.7 {refl} {refl} [] & ∅)
_ = refl

_ : G1 [ # 1 ] ≡ ( node NA4 0.5 {refl} {refl} ((эксперт , # 1) ∷ (говорит , # 0) ∷ []) &
                   node NS2 1.0 {refl} {refl} [] & node NS1 0.7 {refl} {refl} [] &
                   ∅
                 )
_ = refl

_ : roots G1 ≡ (_ , (Ln NS3 _)) ∷ []
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





-- N2 ---- <N4> ---∙ 
--         /        \
-- N1 ----∙          N3
--                  /
-- N5 ---- <N6> ---∙ 
G2 : AGraph _
G2 =
     node0 NS3 ((объяснение , # 0) ∷ (поддержка  , # 2) ∷ []) &
     node NA6 0.4 {refl} {refl} ((факт  , # 0) ∷ []) &
     node NS5 0.6 {refl} {refl} [] &
     node NA4 0.5 {refl} {refl} ((эксперт  , # 1) ∷ (говорит , # 0) ∷ []) & -- missed: область
     node NS2 1.0 {refl} {refl} [] &
     node NS1 0.7 {refl} {refl} [] &
     ∅

-- part of G2, actually
G3 : AGraph _
G3 =
     node NA4 0.5 {refl} {refl} ((эксперт  , # 1) ∷ (говорит , # 0) ∷ []) &
     node NS2 1.0 {refl} {refl} [] &
     node NS1 0.7 {refl} {refl} [] &
     ∅

_ : nodes G2 ≡ (# 0 , (Ln NS3 _)) ∷v (# 1 , (Ln NA6 _)) ∷v (# 2 , (Ln NS5 _)) ∷v (# 3 , (Ln NA4 _))
            ∷v (# 4 , (Ln NS2 _)) ∷v (# 5 , (Ln NS1 _)) ∷v []v
_ = refl

_ : edges G2 ≡ (# 0 , объяснение , # 0) ∷ (# 0 , поддержка , # 2)
             ∷ (# 1 , факт , # 0) 
             ∷ (# 3 , эксперт , # 1) ∷ (# 3 , говорит , # 0)
             ∷ []
_ = refl


_ : preds G2 (# 0) ≡ []
_ = refl

_ : preds G2 (# 3) ≡ (# 0 , поддержка) ∷ []
_ = refl

_ : preds G2 (# 5) ≡ (# 3 , эксперт) ∷ []
_ = refl


_ : NArgs G2 (# 0) ≡ record { Scheme = A-абдукция
                            ; NPremises = just (Ln NS5 _) ∷v []v
                            ; NConclusion = just (Ln NS3 _)
                            } ∷
                     record { Scheme = A-от-эксперта
                            ; NPremises = just (Ln NS1 _) ∷v just (Ln NS2 _) ∷v nothing ∷v []v
                            ; NConclusion = just (Ln NS3 _)
                            } ∷ []
_ = refl

_ : NArgs+ G2 (# 0) ≡ (поддержка , # 2) ∷ []
_ = refl

_ : NArgs- G2 (# 0) ≡ []
_ = refl

_ : NArgs G2 (# 4) ≡ []
_ = refl

_ : roots G2 ≡ (# 0 , (Ln NS3 _)) ∷ []
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

_ : G2 ! (# 0) ≡ context (Ln NS3 nothing) ((объяснение , # 0) ∷ (поддержка , # 2) ∷ [])
_ = refl

_ : G2 ! (# 1) ≡ node NA6 0.4 {refl} {refl} ((факт     , # 0) ∷ [])
_ = refl

_ : G2 ![ (# 0) > (# 0) ] ≡ node NA6 0.4 {refl} {refl} ((факт     , # 0) ∷ [])
_ = refl

_ : G2 ![ (# 1) > (# 2) ] ≡ node NS2 1.0 {refl} {refl} []
_ = refl


G20 = compute G2

G21 = steps 1 G2

G22 = steps 2 G2

G23 = steps 3 G2

G24 = steps 4 G2

G2lim = steps 100 G2



-- N2 ---- <N4> ---∙ 
--         /        \
-- N1 ----∙          N3
--                  /|
-- N5 ---- <N6> ---∙ |
--                   |
-- N7 ---- <N8> -----∙
G4 : AGraph _
G4 =
     node0 NS3 ((объяснение , # 0) ∷ (поддержка , # 2) ∷ (поддержка , # 4) ∷ []) &
     node NA8 0.9 {refl} {refl} ((все-признают , # 0) ∷ []) &
     node NS7 0.9 {refl} {refl} [] &
     node NA6 0.4 {refl} {refl} ((факт     , # 0) ∷ []) &
     node NS5 0.6 {refl} {refl} [] &
     node NA4 0.5 {refl} {refl} ((эксперт  , # 1) ∷ (говорит , # 0) ∷ []) &
     node NS2 1.0 {refl} {refl} [] &
     node NS1 0.7 {refl} {refl} [] &
     ∅

_ : nodes G4 ≡ (# 0 , (Ln NS3 _)) ∷v (# 1 , (Ln NA8 _)) ∷v (# 2 , (Ln NS7 _))
            ∷v (# 3 , (Ln NA6 _)) ∷v (# 4 , (Ln NS5 _)) ∷v (# 5 , (Ln NA4 _))
            ∷v (# 6 , (Ln NS2 _)) ∷v (# 7 , (Ln NS1 _)) ∷v []v
_ = refl

_ : edges G4 ≡ (# 0 , объяснение , # 0)
             ∷ (# 0 , поддержка , # 2) ∷ (# 0 , поддержка , # 4)
             ∷ (# 1 , все-признают , _)
             ∷ (# 3 , факт , # 0) 
             ∷ (# 5 , эксперт , # 1) ∷ (# 5 , говорит , # 0)
             ∷ []
_ = refl


_ : preds G4 (# 0) ≡ []
_ = refl

_ : preds G4 (# 3) ≡ (# 0 , поддержка) ∷ []
_ = refl

_ : preds G4 (# 1) ≡ (# 0 , объяснение) ∷ []
_ = refl

_ : preds G4 (# 7) ≡ (# 5 , эксперт) ∷ []
_ = refl


-- all inputs
_ : Arg G4 (# 0) (# 4) ≡ just record { Scheme = A-от-эксперта
                                     ; NPremises = just (Ln NS1 _) ∷v just (Ln NS2 _) ∷v nothing ∷v []v
                                     ; NConclusion = just (Ln NS3 _)
                                     }
_ = refl

_ : NArgs G4 (# 0) ≡ record { Scheme = A-ad-populum
                            ; NPremises = just (Ln NS7 _) ∷v []v
                            ; NConclusion = just (Ln NS3 _)
                            } ∷
                     record { Scheme = A-абдукция
                            ; NPremises = just (Ln NS5 _) ∷v []v
                            ; NConclusion = just (Ln NS3 _)
                            } ∷
                     record { Scheme = A-от-эксперта
                            ; NPremises = just (Ln NS1 _) ∷v just (Ln NS2 _) ∷v nothing ∷v []v
                            ; NConclusion = just (Ln NS3 _)
                            } ∷ []
_ = refl

-- only attacks
_ : NArgs- G4 (# 0) ≡ []
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

_ : roots G4 ≡ (# 0 , (Ln NS3 _)) ∷ []
_ = refl


-- indexes

_ : G4 ! (# 0) ≡ context (Ln NS3 nothing) ((объяснение , _) ∷ (поддержка , _) ∷ (поддержка , _) ∷ [])
_ = refl

_ : G4 ! (# 3) ≡ node NA6 0.4 ((факт     , _) ∷ [])
_ = refl

_ : G4 ![ (# 0) > (# 2) ] ≡ node NA6 0.4 ((факт     , _) ∷ [])
_ = refl

_ : G4 ![ (# 3) > (# 2) ] ≡ node NS2 1.0 {refl} {refl} []
_ = refl


G40 = compute G4

G41 = steps 1 G4

G4lim = steps 100 G4




-- Graph with conflicts  --------------------------------------------

-- N2 ---- <N4> ---∙ 
--         /        \
-- N1 ----∙          N3 -∙ 
--         \        /|    \
-- N5 ---- <N6> ---∙ CN1  CN2
--                   |    /
-- N7 ---- <N8> ----¬N3 -∙ 
G5 : AGraph _
G5 =
     node NC1 1.0 {refl} {refl} ((conflicted , # 0) ∷ (conflicting , # 3) ∷ []) &
     node0 ¬NS3 ((поддержка , # 0) ∷ []) &
     node NA8 0.9 {refl} {refl} ((все-признают , # 0) ∷ []) &
     node NS7 0.9 {refl} {refl} [] &
     G2                -- missed область in A-от-эксперта !

G6 : AGraph _
G6 =
     node NC2 1.0 {refl} {refl} ((conflicted , # 4) ∷ (conflicting , # 1) ∷ []) &
     G5


_ : nodes G5 ≡ (# 0 , (Ln NC1 _)) ∷v (# 1 , (Ln ¬NS3 _)) ∷v (# 2 , (Ln NA8 _)) ∷v (# 3 , (Ln NS7 _))
            ∷v (# 4 , (Ln NS3 _)) ∷v (# 5 , (Ln NA6 _))  ∷v (# 6 , (Ln NS5 _)) ∷v (# 7 , (Ln NA4 _))
            ∷v (# 8 , (Ln NS2 _)) ∷v (# 9 , (Ln NS1 _))  ∷v []v
_ = refl

_ : roots G5 ≡ (# 0 , (Ln NC1 _)) ∷ []
_ = refl

_ : roots¬CA G5 ≡ (# 1 , (Ln ¬NS3 _)) ∷ (# 4 , (Ln NS3 _)) ∷ []
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

G54 = steps 4 G5

G5100 = steps 100 G5

G5200 = steps 200 G5




G60 = compute G6

G61 = steps 1 G6

G62 = steps 2 G6

G63 = steps 3 G6

G64 = steps 4 G6

G6100 = steps 100 G6

G6200 = steps 200 G6




-- Graph with 2 opposite conflicts  --------------------------------------------

-- N1 ---CN1, CN2--- N2

G7 : AGraph _
G7 =
     node NC2 1.0 {refl} {refl} ((conflicted , # 2) ∷ (conflicting , # 1) ∷ []) &
     node NC1 1.0 {refl} {refl} ((conflicted , # 0) ∷ (conflicting , # 1) ∷ []) &
     node NS2 1.0 {refl} {refl} [] &
     node NS1 1.0 {refl} {refl} [] &
     ∅

G70 = compute G7

G71 = steps 1 G7

G72 = steps 2 G7

G73 = steps 3 G7

G74 = steps 4 G7

G7100 = steps 100 G7

G7200 = steps 200 G7




------------------------------------------------------------------------

open import ShowDAG la

open import IO

w = 110
ws = 90 -- "section" title width

printG1 : AGraph 4 → (∀ {n} → AGraph n → Fin n → MC) → String
printG1 g f = "\nN1  = " +++ pprint w (f g (# 3))
          +++ "  N2  = " +++ pprint w (f g (# 2))
          +++ "  N3  = " +++ pprint w (f g (# 0))
          +++ "  N4  = " +++ pprint w (f g (# 1))
printG2 : AGraph 6 → (∀ {n} → AGraph n → Fin n → MC) → String
printG2 g f = "\nN1  = " +++ pprint w (f g (# 5))
          +++ "  N2  = " +++ pprint w (f g (# 4))
          +++ "  N3  = " +++ pprint w (f g (# 0))
          +++ "  N4  = " +++ pprint w (f g (# 3))
          +++ "\nN5  = " +++ pprint w (f g (# 2))
          +++ "  N6  = " +++ pprint w (f g (# 1))
printG4 : AGraph 8 → (∀ {n} → AGraph n → Fin n → MC) → String
printG4 g f = "\nN1 = " +++ pprint w (f g (# 7))
          +++ "  N2 = " +++ pprint w (f g (# 6))
          +++ "  N3 = " +++ pprint w (f g (# 0))
          +++ "  N4 = " +++ pprint w (f g (# 5))
          +++ "\nN5 = " +++ pprint w (f g (# 4))
          +++ "  N6 = " +++ pprint w (f g (# 3))
          +++ "  N7 = " +++ pprint w (f g (# 2))
          +++ "  N8 = " +++ pprint w (f g (# 1))
printG5 : AGraph 10 → (∀ {n} → AGraph n → Fin n → MC) → String
printG5 g f = "\nN1  = " +++ pprint w (f g (# 9))
          +++ "  N2  = " +++ pprint w (f g (# 8))
          +++ "  N3  = " +++ pprint w (f g (# 4))
          +++ "  N4  = " +++ pprint w (f g (# 7))
          +++ "  N5  = " +++ pprint w (f g (# 6))
          +++ "\nN6  = " +++ pprint w (f g (# 5))
          +++ "  N7  = " +++ pprint w (f g (# 3))
          +++ "  N8  = " +++ pprint w (f g (# 2))
          +++ "  -N3 = " +++ pprint w (f g (# 1))
          +++ "  CN1 = " +++ pprint w (f g (# 0))
printG6 : AGraph 11 → (∀ {n} → AGraph n → Fin n → MC) → String
printG6 g f = "\nN1  = " +++ pprint w (f g (# 10))
          +++ "  N2  = " +++ pprint w (f g (# 9))
          +++ "  N3  = " +++ pprint w (f g (# 5))
          +++ "  N4  = " +++ pprint w (f g (# 8))
          +++ "\nN5  = " +++ pprint w (f g (# 7))
          +++ "  N6  = " +++ pprint w (f g (# 6))
          +++ "  N7  = " +++ pprint w (f g (# 4))
          +++ "  N8  = " +++ pprint w (f g (# 3))
          +++ "\n-N3 = " +++ pprint w (f g (# 2))
          +++ "  CN1 = " +++ pprint w (f g (# 1))
          +++ "  CN2 = " +++ pprint w (f g (# 0))
printG7 : AGraph 4 → (∀ {n} → AGraph n → Fin n → MC) → String
printG7 g f = "\nN1  = " +++ pprint w (f g (# 3))
          +++ "  N2  = " +++ pprint w (f g (# 2))
          +++ "  CN1 = " +++ pprint w (f g (# 1))
          +++ "  CN2 = " +++ pprint w (f g (# 0))

main = run (putStrLn stringToPrint)
  where
  stringToPrint = S.replicate ws '-'
    -- +++ ppretty ws (docSection ws "G1 orig")
    -- +++ printG1 G1 val←i
    -- +++ ppretty ws (docSection ws "G1 computed")
    -- +++ printG1 G1 val
    -- +++ ppretty ws (docSection ws "G10")
    -- +++ printG1 G10 val←i
    -- +++ ppretty ws (docSection ws "G11")
    -- +++ printG1 G11 val←i
    -- +++ ppretty ws (docSection ws "G12")
    -- +++ printG1 G12 val←i
    -- +++ ppretty ws (docSection ws "G13")
    -- +++ printG1 G13 val←i
    -- +++ ppretty ws (docSection ws "G14")
    -- +++ printG1 G14 val←i
    -- +++ ppretty ws (docSection ws "G1lim")
    -- +++ printG1 G1lim val←i

    -- +++ ppretty ws (docSection ws "G2 orig")
    -- +++ printG2 G2 val←i
    -- +++ ppretty ws (docSection ws "G2 computed")
    -- +++ printG2 G2 val
    -- +++ ppretty ws (docSection ws "G20")
    -- +++ printG2 G20 val←i
    -- -- +++ ppretty ws (docSection ws "G21")
    -- -- +++ printG2 G21 val←i
    -- -- +++ ppretty ws (docSection ws "G22")
    -- -- +++ printG2 G22 val←i
    -- -- +++ ppretty ws (docSection ws "G23")
    -- -- +++ printG2 G23 val←i
    -- -- +++ ppretty ws (docSection ws "G24")
    -- -- +++ printG2 G24 val←i
    -- +++ ppretty ws (docSection ws "G2lim")
    -- +++ printG2 G2lim val←i

    -- +++ pprint 110 G2
    
    -- +++ ppretty ws (docSection ws "G4 orig")
    -- +++ printG4 G4 val←i
    -- +++ ppretty ws (docSection ws "G4 computed")
    -- +++ printG4 G4 val
    -- +++ ppretty ws (docSection ws "G40")
    -- +++ printG4 G40 val←i
    -- +++ ppretty ws (docSection ws "G41")
    -- +++ printG4 G41 val←i
    -- +++ ppretty ws (docSection ws "G4lim")
    -- +++ printG4 G4lim val←i

    -- +++ ppretty ws (docSection ws "G5 orig")
    -- +++ printG5 G5 val←i
    -- +++ ppretty ws (docSection ws "G5 computed")
    -- +++ printG5 G5 val
    -- +++ ppretty ws (docSection ws "G50")
    -- +++ printG5 G50 val←i
    -- +++ ppretty ws (docSection ws "G51")
    -- +++ printG5 G51 val←i
    -- +++ ppretty ws (docSection ws "G52")
    -- +++ printG5 G52 val←i
    -- +++ ppretty ws (docSection ws "G53")
    -- +++ printG5 G53 val←i
    -- +++ ppretty ws (docSection ws "G54")
    -- +++ printG5 G54 val←i
    -- +++ ppretty ws (docSection ws "G5100")
    -- +++ printG5 G5100 val←i
    -- +++ ppretty ws (docSection ws "G5200")
    -- +++ printG5 G5200 val←i

    -- +++ (pprint 110 G5)

    +++ ppretty ws (docSection ws "G6 orig")
    +++ printG6 G6 val←i
    +++ ppretty ws (docSection ws "G6 computed")
    +++ printG6 G6 val
    +++ ppretty ws (docSection ws "G60")
    +++ printG6 G60 val←i
    +++ ppretty ws (docSection ws "G61")
    +++ printG6 G61 val←i
    +++ ppretty ws (docSection ws "G62")
    +++ printG6 G62 val←i
    +++ ppretty ws (docSection ws "G63")
    +++ printG6 G63 val←i
    +++ ppretty ws (docSection ws "G64")
    +++ printG6 G64 val←i
    +++ ppretty ws (docSection ws "G6100")
    +++ printG6 G6100 val←i
    +++ ppretty ws (docSection ws "G6200")
    +++ printG6 G6200 val←i

    -- +++ (pprint 110 G6)

    +++ ppretty ws (docSection ws "G7 orig")
    +++ printG7 G7 val←i
    +++ ppretty ws (docSection ws "G7 computed")
    +++ printG7 G7 val
    +++ ppretty ws (docSection ws "G70")
    +++ printG7 G70 val←i
    +++ ppretty ws (docSection ws "G71")
    +++ printG7 G71 val←i
    +++ ppretty ws (docSection ws "G72")
    +++ printG7 G72 val←i
    +++ ppretty ws (docSection ws "G73")
    +++ printG7 G73 val←i
    +++ ppretty ws (docSection ws "G74")
    +++ printG7 G74 val←i
    +++ ppretty ws (docSection ws "G7100")
    +++ printG7 G7100 val←i
    +++ ppretty ws (docSection ws "G7200")
    +++ printG7 G7200 val←i

    +++ (pprint 110 G7)

    -- +++ "\nN1+N2 = " +++ pprint w (val←Ctx G2 (# 5) ⟪ _⊕_ Pref ⟫ val←Ctx G2 (# 4))
    -- +++ "\nN4+N6 = " +++ pprint w (val←Ctx G2 (# 3) ⟪ _⊕_ Pref ⟫ val←Ctx G2 (# 1))
    -- +++ "\nN1+N5 = " +++ pprint w (val←Ctx G2 (# 5) ⟪ _⊕_ Pref ⟫ val←Ctx G2 (# 2))
    -- +++ "\nN1.N2 = " +++ pprint w (val←Ctx G2 (# 5) ⟪ _⊙_ Pref ⟫ val←Ctx G2 (# 4))
    -- +++ "\nN4.N6 = " +++ pprint w (val←Ctx G2 (# 3) ⟪ _⊙_ Pref ⟫ val←Ctx G2 (# 1))
    -- +++ "\nN1.N5 = " +++ pprint w (val←Ctx G2 (# 5) ⟪ _⊙_ Pref ⟫ val←Ctx G2 (# 2))
    -- -- +++ "\nNConflicts 0: " +++ "" +++ pprint w (NConflicts G5 (# 0))
    -- -- +++ "\nNConflicts 1: " +++ "" +++ pprint w (NConflicts G5 (# 1))
    -- -- +++ "\nNConflicts 2: " +++ "" +++ pprint w (NConflicts G5 (# 2))
    -- -- +++ "\nNConflicts 3: " +++ "" +++ pprint w (NConflicts G5 (# 3))
    -- -- +++ "\nNConflicts 4: " +++ "" +++ pprint w (NConflicts G5 (# 4))
    -- +++ "\nG5repl0  ======================="
    -- +++ "\nN1 = " +++ pprint w (val←i (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 7))
    -- +++ "\nN2 = " +++ pprint w (val←i (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 6))
    -- +++ "\nN3 = " +++ pprint w (val←i (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 0))
    -- +++ "\nN4 = " +++ pprint w (val←i (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 5))
    -- +++ "\nN5 = " +++ pprint w (val←i (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 4))
    -- +++ "\nN6 = " +++ pprint w (val←i (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 3))
    -- +++ "\nN7 = " +++ pprint w (val←i (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 2))
    -- +++ "\nN8 = " +++ pprint w (val←i (replaceInGraph G5 (# 0) (just (LA⊤ Pref))) (# 1))
    -- +++ "\nG5repl2  ======================="
    -- +++ "\nN1 = " +++ pprint w (val←i (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 7))
    -- +++ "\nN2 = " +++ pprint w (val←i (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 6))
    -- +++ "\nN3 = " +++ pprint w (val←i (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 0))
    -- +++ "\nN4 = " +++ pprint w (val←i (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 5))
    -- +++ "\nN5 = " +++ pprint w (val←i (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 4))
    -- +++ "\nN6 = " +++ pprint w (val←i (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 3))
    -- +++ "\nN7 = " +++ pprint w (val←i (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 2))
    -- +++ "\nN8 = " +++ pprint w (val←i (replaceInGraph G5 (# 2) (just (LA⊤ Pref))) (# 1))
    -- +++ "\nG5repl7  ======================="
    -- +++ "\nN1 = "
