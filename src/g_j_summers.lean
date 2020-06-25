/-
Copyright (c) 2020 Dan Stanescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Dan Stanescu.
-/

-- Just getting started

inductive gender
| male
| female

inductive status
| alone
| together

inductive participant
| gender
| state

structure the_cast_1 := ( p₁ p₂ p₃ p₄ p₅ : participant )
variable c : the_cast_1
variable p : participant
#check c.1 = participant.gender


-- this seems better
structure actor := (g : gender) (s : status)
structure the_cast := ( Ali Hus Son Dau Bro : actor )


variable a : the_cast
def a.Ali.gender := gender.female 
#check a.1.g = gender.male


