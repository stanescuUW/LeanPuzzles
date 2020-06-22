import tactic

inductive person
| knight
| knave

notation `y` := person.knight
notation `n` := person.knave

structure Q := (p₁ p₂ : person)

def Q1 := Q

namespace Q1

variables (q : Q1)

def D1 := q.1 = n ∧ q.2 = n

def H := (q.1 = y ∧ q.D1) ∨ (q.1 = n ∧ ¬ q.D1)

lemma answer : q.H → q.1 = n ∧ q.2 = y :=
begin
    rcases q with ⟨_|_,_|_⟩,
    { simp [H, D1], },
    { simp [H, D1], },
    { simp [H, D1], },
    { simp [H, D1], },
    done
end



end Q1

