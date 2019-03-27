module ArgSchemes where

open import Data.Unit
-- open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.List
open import Data.String renaming (_++_ to _+++_)
open import Data.Maybe
open import Data.Float


record Thesis' : Set where
  field
    pos : String  -- positive form
    neg : String  -- negative form

data Thesis : Set where
  Pos : Thesis' → Thesis -- тезис
  Neg : Thesis → Thesis  -- отрицание тезиса
  Th  : String → Thesis  -- если  отрицание не определено / не требуется

record Statement : Set where
  constructor st
  field
    text   : Maybe String  -- сам текст
    thesis : Thesis        -- его смысл / расшифровка (пропозиция)
    weight : Float

------------  Определение схем аргументов  ----------

data Argument : Set 

record A-от-эксперта : Set where
  field
    эксперт : Statement
    говорит : Statement
    область : Statement 
    цель    : Statement
    Q1      : Maybe Statement

record A-от-примера : Set where
  field
    пример : Statement
    цель   : Statement

record A-от-причины-к-следствию : Set where
  field
    причинная-связь : Statement
    причина         : Statement
    цель            : Statement
    
record A-от-следствия-к-причине : Set where
  field
    причинная-связь : Statement
    следствие       : Statement
    цель            : Statement

record A-от-знака : Set where
  field
    знак            : Statement
    связь-со-знаком : Statement
    цель            : Statement

record A-абдукция : Set where
  field
    факт       : Statement
    объяснение : Statement
    цель       : Statement
    
record A-ad-hominem : Set where
  field
    плохой-человек : Statement
    говорит        : Statement
    цель           : Statement

record A-ad-hominem-arg : Set where
  inductive
  field
    плохой-человек : Statement
    аргумент       : Argument
    цель           : Argument

record A-от-альтернативы : Set where
  field
    альтернатива : Statement
    неверно      : Statement
    цель         : Statement
    
data Argument where
  `dummy : Argument
  `от-эксперта : A-от-эксперта → Argument
  `от-примера : A-от-примера → Argument
  `от-причины-к-следствию : A-от-причины-к-следствию → Argument
  `от-следствия-к-причине : A-от-следствия-к-причине → Argument
  `от-знака : A-от-знака → Argument
  `абдукция : A-абдукция → Argument
  `ad-hominem : A-ad-hominem → Argument
  `ad-hominem-arg : A-ad-hominem-arg → Argument
  `от-альтернативы : A-от-альтернативы → Argument

-- Имена схем

AName : Argument → String
AName `dummy = "DUMMY ARGUMENT"
AName (`от-эксперта a) = "От эксперта"
AName (`от-примера a) = "От примера"
AName (`от-причины-к-следствию a) = "От причины к следствию"
AName (`от-следствия-к-причине a) = "От следствия к причине"
AName (`от-знака a) = "От знака"
AName (`абдукция a) = "Абдукция"
AName (`ad-hominem a) = "Ad hominem (против тезиса)"
AName (`ad-hominem-arg a) = "Ad hominem (против аргумента)"
AName (`от-альтернативы a) = "От альтернативы"



--  подготовка строк для печати

ThString : Thesis → String
ThString (Pos t) = Thesis'.pos t
ThString (Neg (Pos t)) = Thesis'.neg t
ThString (Neg (Neg t)) = ThString t
ThString (Th s) = s
ThString (Neg (Th s)) = "NOT DEFINED"


StString : String → Statement → String
StString pre (st nothing th wt) = "\n"
  +++ pre +++ "THESIS: " +++ ThString th +++ " (" +++ primShowFloat wt +++ ") " 
StString pre (st (just t) th wt) = "\n"
  +++ pre +++ "TEXT:   " +++ t +++ "\n"
  +++ pre +++ "THESIS: " +++ ThString th +++ " (" +++ primShowFloat wt +++ ") " 


concl-line = "----------"
dpre : String → String
dpre pre = pre +++ pre
npre : String → String
npre pre = "\n" +++ pre

AString : String → Argument → String
AString _ `dummy = "DUMMY"
AString pre (`от-эксперта a) =
  npre pre +++ "эксперт: " +++ StString (dpre pre) (A-от-эксперта.эксперт a)
  +++ npre pre +++ "говорит: " +++ StString (dpre pre) (A-от-эксперта.говорит a)
  +++ npre pre +++ "область: " +++ StString (dpre pre) (A-от-эксперта.область a)
  +++ npre pre +++ concl-line
  +++ pre +++ StString pre (A-от-эксперта.цель  a)
AString pre (`от-примера a) =
  npre pre +++ "пример: " +++ StString (dpre pre) (A-от-примера.пример a)
  +++ npre pre +++ concl-line
  +++ pre +++ StString pre (A-от-примера.цель  a)
AString pre (`от-причины-к-следствию a) =
  npre pre
  +++ "причинная связь: " +++ StString (dpre pre) (A-от-причины-к-следствию.причинная-связь a)
  +++ npre pre +++ "причина: " +++ StString (dpre pre) (A-от-причины-к-следствию.причина a)
  +++ npre pre +++ concl-line
  +++ pre +++ StString pre (A-от-причины-к-следствию.цель  a)
AString pre (`от-следствия-к-причине a) =
  npre pre
  +++ "причинная связь: " +++ StString (dpre pre) (A-от-следствия-к-причине.причинная-связь a)
  +++ npre pre +++ "следствие: " +++ StString (dpre pre) (A-от-следствия-к-причине.следствие a)
  +++ npre pre +++ concl-line
  +++ pre +++ StString pre (A-от-следствия-к-причине.цель  a)
AString pre (`от-знака a) =
  npre pre +++ "знак: " +++ StString (dpre pre) (A-от-знака.знак a)
  +++ npre pre +++ "связь-со-знаком: " +++ StString (dpre pre) (A-от-знака.связь-со-знаком a)
  +++ npre pre +++ concl-line
  +++ pre +++ StString pre (A-от-знака.цель  a)
AString pre (`абдукция a) =
  npre pre +++ "факт: " +++ StString (dpre pre) (A-абдукция.факт a)
  +++ npre pre +++ "объяснение: " +++ StString (dpre pre) (A-абдукция.объяснение a)
  +++ npre pre +++ concl-line
  +++ pre +++ StString pre (A-абдукция.цель  a)
AString pre (`ad-hominem a) =
  npre pre +++ "плохой человек: " +++ StString (dpre pre) (A-ad-hominem.плохой-человек a)
  +++ npre pre +++ "говорит: " +++ StString (dpre pre) (A-ad-hominem.говорит a)
  +++ npre pre +++ concl-line
  +++ pre +++ StString pre (A-ad-hominem.цель  a)
AString pre (`ad-hominem-arg a) =
  npre pre +++ "плохой человек: " +++ StString (dpre pre) (A-ad-hominem-arg.плохой-человек a)
  +++ npre pre +++ "аргумент: " +++ AString (dpre pre) (A-ad-hominem-arg.аргумент a)
  +++ npre pre +++ concl-line
  +++ npre pre +++ "Аргумент сомнителен"
AString pre (`от-альтернативы a) =
  npre pre +++ "альтернатива: " +++ StString (dpre pre) (A-от-альтернативы.альтернатива a)
  +++ npre pre +++ "неверно: " +++ StString (dpre pre) (A-от-альтернативы.неверно a)
  +++ npre pre +++ concl-line
  +++ pre +++ StString pre (A-от-альтернативы.цель  a)

