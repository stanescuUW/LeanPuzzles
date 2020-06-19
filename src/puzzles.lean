import tactic

inductive door_leads_to
| lady
| tiger

notation `y` := door_leads_to.lady
notation `n` := door_leads_to.tiger

structure Q := (d₁ d₂ : door_leads_to)

def Q1 := Q

namespace Q1

variables (q : Q1)
#check q
#check Q1
#check Q
#check Q.d₁
#check q.d₁
variable p : Q
#check p.1
lemma qq : Q = Q1 := rfl

def D1 := q.1 = y ∧ q.2 = n

def D2 := (q.1 = y ∨ q.2 = y) ∧ (q.1 = n ∨ q.2 = n)

def H := q.D1 ∧ ¬q.D2 ∨ ¬q.D1 ∧ q.D2

lemma answer_term : q.H → q.1 = n ∧ q.2 = y :=
by rcases q with ⟨_|_,_|_⟩; simp [H, D1, D2]
#print answer_term

lemma answer_tactic1 : q.H → q.1 = n ∧ q.2 = y :=
begin
    intro h,
    split,
    cases h with h1 h2,
    cases h1 with h11 h12,
    cases h11 with h111 h112,
    simp [D2] at h12,
    have g1 : q.d₁ = y ∨ q.d₂ = y, from or.inl h111,
    --have g2 : h12 g1,
    cases g1 with ha hb, sorry, sorry, sorry, sorry, 
end

lemma answer_tactic2 : q.H → q.1 = n ∧ q.2 = y :=
begin
    rcases q with ⟨_|_,_|_⟩;
    simp [H, D1, D2],
    done
end

lemma answer_tactic3: q.H → q.1 = n ∧ q.2 = y :=
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