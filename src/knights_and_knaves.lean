import tactic

/-
Knights and knaves puzzles by R. Smullyan.
There is an island where all inhabitants are either knights or knaves. 
Knights always tell the truth. Knaves always lie.
Jack and Bill are two inhabitants of this island.
-/

inductive person
| knight
| knave

notation `y` := person.knight
notation `n` := person.knave

structure Q := (p₁ p₂ : person)

/-
In this first puzzle, only Jack makes a statement.
He affirms that both our heroes (i.e. both Jack and Bill) are knaves.
What kind of islanders are they?
-/

def Q1 := Q

namespace Q1

variables (q : Q1)

def S1 := q.1 = n ∧ q.2 = n

def H := (q.1 = y ∧ q.S1) ∨ (q.1 = n ∧ ¬ q.S1)

lemma answer : q.H → q.1 = n ∧ q.2 = y :=
begin
    rcases q with ⟨_|_,_|_⟩;
    { simp [H, S1], },
    done
end

end Q1

/-
In the second puzzle, both Jack and Bill make a statement.
Jack states that he's a knave if and only if Bill is a knave.
Bill states that they are different kinds. 
Again, what kind of islanders are our protagonists?
-/


def Q2 := Q

namespace Q2

variables (q : Q2)

def S1 := q.2 = n ↔ q.1 = n
def S2 := q.1 = y ∧ q.2 = n ∨ q.1 = n ∧ q.2 = y

def H1 := (q.1 = y ∧ q.S1) ∨ (q.1 = n ∧ ¬ q.S1)
def H2 := (q.2 = y ∧ q.S2) ∨ (q.2 = n ∧ ¬ q.S2)
def H := q.H1 ∧ q.H2

lemma answer : q.H → q.1 = n ∧ q.2 = y :=
begin
    rcases q with ⟨_|_,_|_⟩;
    { simp [H, H1, S1, H2, S2], },
    done
end


end Q2

