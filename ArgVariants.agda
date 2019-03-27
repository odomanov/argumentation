module ArgVariants where

open import Data.Unit
-- open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.List
open import Data.String renaming (_++_ to _+++_)
open import Data.Maybe
open import Data.Float

open import ArgSchemes

------------  Варианты аргументов  ----------

T-P-говорит-что-A-истинно = Th "P говорит, что A истинно (ложно)"
T-A-истинно = Th "A истинно (ложно)"
T-A-имеет-место = Pos record {
    pos = "A имеет место";
    neg = "A не имеет места" }
T-B-имеет-место = Pos record {
    pos = "B имеет место";
    neg = "B не имеет места" }
T-B-будет-иметь-место = Pos record {
    pos = "B будет иметь место / должно случиться";
    neg = "B не будет иметь места / не должно случиться" }
T-в-частном-случае-A-истинно = Th "A истинно (ложно) в частном случае"
T-A-истинно-в-общем-случае = Th "A истинно (ложно) в общем случае"

V-от-эксперта =
  let instance
       aa : A-от-эксперта
       aa = record {
         эксперт = record {
           text = nothing;
           thesis = Th "P является экспертом в области D";
           weight = 0.5 };
         говорит = record {
           text = nothing;
           thesis = T-P-говорит-что-A-истинно;
           weight = 0.5 };  
         область = record {
           text = nothing;
           thesis = Th "A относится к области D";
           weight = 0.5 };
         цель = record {
           text = nothing;
           thesis = T-A-истинно;
           weight = 0.5 };
         Q1 = nothing }
  in `от-эксперта aa

-- V-от-эксперта-neg =
--   let instance
--        aa : A-от-эксперта
--        aa = record {
--          эксперт = record {
--            text = nothing;
--            thesis = Th "P является экспертом в области D";
--            weight = 0.5 };
--          говорит = record {
--            text = nothing;
--            thesis = Neg T-P-говорит-что-A-истинно;
--            weight = 0.5 };
--          область = record {
--            text = nothing;
--            thesis = Th "A относится к области D";
--            weight = 0.5 };
--          цель = record {
--            text = nothing;
--            thesis = Neg T-A-истинно;
--            weight = 0.5 };
--          Q1 = nothing }
--   in `от-эксперта aa

V-от-примера =
  let instance
       aa : A-от-примера
       aa = record {
         пример = record {
           text = nothing;
           thesis = T-в-частном-случае-A-истинно;
           weight = 0.5 };
         цель = record {
           text = nothing;
           thesis = T-A-истинно-в-общем-случае;
           weight = 0.5 } }
 in `от-примера aa

-- V-от-примера-neg =
--   let instance
--        aa : A-от-примера
--        aa = record {
--          пример = record {
--            text = nothing;
--            thesis = Neg T-в-частном-случае-A-истинно;
--            weight = 0.5 };
--          цель = record {
--            text = nothing;
--            thesis = Neg T-A-истинно-в-общем-случае;
--            weight = 0.5 } }
--  in `от-примера aa

V-от-причины-к-следствию =
  let instance
       aa : A-от-причины-к-следствию
       aa = record {
         причинная-связь = record {
           text = nothing;
           thesis = Th "A вызывает B";
           weight = 0.5 };
         причина = record {
           text = nothing;
           thesis = T-A-имеет-место;
           weight = 0.5 };
         цель = record {
           text = nothing;
           thesis = T-B-будет-иметь-место;
           weight = 0.5 } }
  in `от-причины-к-следствию aa

V-от-следствия-к-причине =
  let instance
       aa : A-от-следствия-к-причине
       aa = record {
         причинная-связь = record {
           text = nothing;
           thesis = Th "A вызывает B";
           weight = 0.5 };
         следствие = record {
           text = nothing;
           thesis = T-B-имеет-место;
           weight = 0.5 };
         цель = record {
           text = nothing;
           thesis = T-A-имеет-место;
           weight = 0.5 } }
  in `от-следствия-к-причине aa

V-от-следствия-к-причине-neg =
  let instance
       aa : A-от-следствия-к-причине
       aa = record {
         причинная-связь = record {
           text = nothing;
           thesis = Th "A вызывает B";
           weight = 0.5 };
         следствие = record {
           text = nothing;
           thesis = Neg T-B-имеет-место;
           weight = 0.5 };
         цель = record {
           text = nothing;
           thesis = Neg T-A-имеет-место;
           weight = 0.5 } }
  in `от-следствия-к-причине aa

V-от-знака =
  let instance
       aa : A-от-знака
       aa = record {
         знак = record {
           text = nothing;
           thesis = Th "A имеет место";
           weight = 0.5 };
         связь-со-знаком = record {
           text = nothing;
           thesis = Th "A является индикатором B";
           weight = 0.5 };
         цель = record {
           text = nothing;
           thesis = Th "B имеет место";
           weight = 0.5 } }
  in `от-знака aa

V-абдукция =
  let instance
       aa : A-абдукция
       aa = record {
         факт = record {
           text = nothing;
           thesis = Th "A имеет место";
           weight = 0.5 };
         объяснение = record {
           text = nothing;
           thesis = Th "B лучше всего объясняет A";
           weight = 0.5 };
         цель = record {
           text = nothing;
           thesis = Th "Имеет место B";
           weight = 0.5 } }
  in `абдукция aa

V-ad-hominem =
  let instance
       aa : A-ad-hominem
       aa = record {
         плохой-человек = record {
           text = nothing;
           thesis = Th "P плохой человек";
           weight = 0.5 };
         говорит = record {
           text = nothing;
           thesis = Th "P говорит, что A истинно";
           weight = 0.5 };
         цель = record {
           text = nothing;
           thesis = Th "A ложно";
           weight = 0.5 } }
  in `ad-hominem aa

V-ad-hominem-arg =
  let instance
       aa : A-ad-hominem-arg
       aa = record {
         плохой-человек = record {
           text = nothing;
           thesis = Th "P плохой человек";
           weight = 0.5 };
         аргумент = `dummy;
         цель = `dummy }
  in `ad-hominem-arg aa

V-от-альтернативы =
  let instance
       aa : A-от-альтернативы
       aa = record {
         альтернатива = record {
           text = nothing;
           thesis = Th "Может иметь место либо X, либо Y";
           weight = 0.5 };
         неверно = record {
           text = nothing;
           thesis = Th "X явно не имеет места";
           weight = 0.5 };
         цель = record {
           text = nothing;
           thesis = Th "Имеет место Y";
           weight = 0.5 } }
  in `от-альтернативы aa

VList = V-от-эксперта ∷ -- V-от-эксперта-neg ∷
        V-от-примера ∷ -- V-от-примера-neg ∷
        V-от-причины-к-следствию ∷
        V-от-следствия-к-причине ∷ V-от-следствия-к-причине-neg ∷
        V-от-знака ∷
        V-абдукция ∷
        V-ad-hominem ∷
        V-ad-hominem-arg ∷
        V-от-альтернативы ∷
        []
      
