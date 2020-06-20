import tactic

/-
The first three puzzles from:
    "The Lady or the Tiger? And Other Logic Puzzles"
        by Raymond Smullyan.
Contributed to the Lean Zulip chat by Yury G. Kudryashov
but apparently set up by his seven-years-old son.
Slightly modified in appearance but not in content.

-/

inductive door_leads_to
| lady
| tiger

notation `y` := door_leads_to.lady
notation `n` := door_leads_to.tiger

structure Q := (d₁ d₂ : door_leads_to)

def Q1 := Q

namespace Q1

variables (q : Q1)

def D1 := q.1 = y ∧ q.2 = n

def D2 := (q.1 = y ∨ q.2 = y) ∧ (q.1 = n ∨ q.2 = n)

def H := q.D1 ∧ ¬q.D2 ∨ ¬q.D1 ∧ q.D2

lemma answer_term : q.H → q.1 = n ∧ q.2 = y :=
by rcases q with ⟨_|_,_|_⟩; simp [H, D1, D2]

lemma answer_tactic : q.H → q.1 = n ∧ q.2 = y :=
begin
    rcases q with ⟨_|_,_|_⟩,
    simp [H], simp [D1], simp [D2],
    simp[H], simp [D1], simp [D2],
    simp [H], 
    simp [H], simp [D1], simp [D2], 
    done
end

end Q1

def Q2 := Q
/- ∧ : \and ∨ : \or ¬ : \not -/

namespace Q2

variables (q : Q2)

def D1 := q.1=y ∨ q.2=y

def D2 := q.1=n

def H := q.D1∧q.D2 ∨ ¬q.D1∧¬q.D2

lemma answer : q.H → q.1 = n ∧ q.2 = y :=
by rcases q with ⟨_|_,_|_⟩; simp [H, D1, D2]

end Q2

def Q3 := Q
/- ∧ : \and ∨ : \or ¬ : \not -/

namespace Q3

variables (q : Q3)

def D1 := q.1=n∨q.2=y

def D2 := q.1=y

def H := q.D1∧q.D2 ∨ ¬q.D1∧¬q.D2

lemma answer : q.H → q.1 = y ∧ q.2 = y :=
by rcases q with ⟨_|_,_|_⟩; simp [H, D1, D2]

end Q3