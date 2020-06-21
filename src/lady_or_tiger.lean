import tactic

/-
The first three puzzles from:
    "The Lady or the Tiger? And Other Logic Puzzles"
        by Raymond Smullyan.
Contributed to the Lean Zulip chat by Yury G. Kudryashov
but apparently set up by his seven-years-old son.
Slightly modified in appearance (for readability) but not in content.
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

/-
Puzzles 4-7 from the same book:
    "The Lady or the Tiger? And Other Logic Puzzles"
        by Raymond Smullyan.
Solutions written by D. Stanescu in the same framework as above. 
In these puzzles, the king explains that the sign on the first door (D1) is true if a lady
is in in that room and is false if a tiger is in that room. The opposite is true for the sign on 
the second door (D2), which is true if a tiger is hidden behind it but false otherwise.
-/

/-
Puzzle number four: 
First door sign reads: "Both rooms contain ladies." 
Second door sign reads: "Both rooms contain ladies."
-/

def Q4 := Q
/- ∧ : \and ∨ : \or ¬ : \not -/

namespace Q4

variables (q : Q4)

def D1 := q.1=y ∧ q.2=y

def D2 := q.1=y ∧ q.2=y

-- one way to set up this problem 
def H1 := q.1 = y ∧ q.D1 ∨ q.1 = n ∧ ¬ q.D1
def H2 := q.2 = y ∧ ¬ q.D2 ∨ q.2 = n ∧ q.D2
def H := q.H1 ∧ q.H2

lemma answer1 : q.H → q.1 = n ∧ q.2 = y :=
begin
    rcases q with ⟨_|_,_|_⟩,
    simp [H], simp [H1], simp [D1], simp [H2], simp [D2], 
    simp [H], simp [H1], simp [D1], 
    simp [H], simp [H1], 
    simp [H], simp [H1], simp [D1], simp [H2], simp [D2], 
    done
end

lemma answer2 : q.H → q.1 = n ∧ q.2 = y :=
begin
    rcases q with ⟨_|_,_|_⟩;
    simp [H, H1, D1, H2, D2], 
    done
end

/-
Puzzle number five: 
First door sign reads: "At least one room contains a lady." 
Second door sign reads: "The other room contains a lady."
-/

end Q4

def Q5 := Q
/- ∧ : \and ∨ : \or ¬ : \not -/

namespace Q5

variables (q : Q5)

def D1 := q.1=y ∨ q.2=y ∨ q.1 = y ∧ q.2 = y

def D2 := q.1=y

-- same setup as Q4 above
def H1 := q.1 = y ∧ q.D1 ∨ q.1 = n ∧ ¬ q.D1
def H2 := q.2 = y ∧ ¬ q.D2 ∨ q.2 = n ∧ q.D2
def H := q.H1 ∧ q.H2

lemma answer : q.H → q.1 = y ∧ q.2 = n :=
begin
    rcases q with ⟨_|_,_|_⟩;
    simp [H, H1, D1, H2, D2], 
    done
end

end Q5

/-
Puzzle number six: 
First door sign reads: "It makes no difference which room you pick." 
Second door sign reads: "There is a lady in the other room."
Apparently he king is particularly fond of this puzzle.
-/

def Q6 := Q
/- ∧ : \and ∨ : \or ¬ : \not -/

namespace Q6

variables (q : Q6)

def D1 := q.1 = q.2

def D2 := q.1=y

-- same setup as Q4 above
def H1 := q.1 = y ∧ q.D1 ∨ q.1 = n ∧ ¬ q.D1
def H2 := q.2 = y ∧ ¬ q.D2 ∨ q.2 = n ∧ q.D2
def H := q.H1 ∧ q.H2

lemma answer : q.H → q.1 = n ∧ q.2 = y :=
begin
    rcases q with ⟨_|_,_|_⟩;
    simp [H, H1, D1, H2, D2], 
    done
end


end Q6
