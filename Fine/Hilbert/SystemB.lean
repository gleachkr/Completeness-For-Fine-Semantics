import Fine.PropositionalLanguage

inductive BTheorem : Form → Type
  | taut {p} : BTheorem (p ⊃ p)
  | andE₁ {p q} : BTheorem (p & q ⊃ p)
  | andE₂ {p q} : BTheorem (p & q ⊃ q)
  | andI {p q r} : BTheorem ((p ⊃ q) & (p ⊃ r) ⊃ (p ⊃ q & r))
  | orI₁ {p q} : BTheorem (p ⊃ p ¦ q)
  | orI₂ {p q} : BTheorem (q ⊃ p ¦ q)
  | orE {p q r} : BTheorem ((p ⊃ r) & (q ⊃ r) ⊃ (p ¦ q ⊃ r))
  | dne {p} : BTheorem (~~p ⊃ p)
  | dist {p q r} : BTheorem (p & (q ¦ r) ⊃ (p & q) ¦ (p & r))
  | mp {p q} (h₁ : BTheorem p) (h₂ : BTheorem (p ⊃ q)) : BTheorem q
  | adj {p q} (h₁ : BTheorem p) (h₂ : BTheorem q) : BTheorem (p & q)
  | cp {p q} (h₁ : BTheorem (p ⊃ ~q)) : BTheorem (q ⊃ ~p)
  | hs {p q r s} (h₁ : BTheorem (p ⊃ q)) (h₂ : BTheorem (r ⊃ s)) : BTheorem ((q ⊃ r) ⊃ (p ⊃ s))
  deriving DecidableEq

inductive BProof : Ctx → Form → Type
  | ax {Γ} {p} (h: p ∈ Γ) : BProof Γ p
  | mp {Γ} {p} {q} (h₁ : BProof Γ p) (h₂ : BTheorem (p ⊃ q)) : BProof Γ q
  | adj {Γ} {p} {q} (h₁ : BProof Γ p) (h₂ : BProof Γ q) : BProof Γ (p & q)
  deriving DecidableEq

section

open BTheorem

variable {p q r s : Form} 

theorem BProof.adjoinPremises { r : Form } : BProof {p,q} r → BProof {p & q} r
  | ax h => if c₁ : r = p then by
              rw [c₁]
              exact mp (ax rfl : BProof {p&q} (p&q)) andE₁
            else if c₂ : r = q then by
              rw [c₂]
              exact mp (ax rfl : BProof {p&q} (p&q)) andE₂
            else False.elim (Or.elim h c₁ c₂)
  | mp h₁ h₂ => mp (adjoinPremises h₁) h₂
  | adj h₁ h₂ => adj (adjoinPremises h₁) (adjoinPremises h₂)

def BTheorem.demorgansLaw : BTheorem ((p & q) ⊃ ~(~p ¦ ~q)) := 
  have l₁ : ∀{r : Form}, BTheorem (r ⊃ ~~r) := cp taut
  have l₂ : BTheorem (~p ⊃ ~(p & q)) := cp $ mp taut (hs andE₁ l₁)
  have l₃ : BTheorem (~q ⊃ ~(p & q)) := cp $ mp taut (hs andE₂ l₁)
  cp $ mp (adj l₂ l₃) orE

def BTheorem.transitivity (h₁ : BTheorem (p ⊃ q)) (h₂ : BTheorem (q ⊃ r)) : BTheorem (p ⊃ r) :=
  mp taut (hs h₁ h₂) 

def BTheorem.fromProof { p q : Form } : BProof {p} q → BTheorem (p ⊃ q)
  | BProof.ax h => by rw [h]; exact taut
  | BProof.adj h₁ h₂ => mp (adj (fromProof h₁) (fromProof h₂)) andI
  | BProof.mp h₁ h₂ => transitivity (fromProof h₁) h₂

def BTheorem.toProof { p q : Form } (h₁ : BTheorem (p ⊃ q)) : BProof {p} q := 
  BProof.mp (BProof.ax rfl) h₁

example : BTheorem ((p ⊃ q) ⊃ (p ⊃ (q ¦ r))) :=
  hs taut orI₁

example : BTheorem ((p ⊃ q) ⊃ (p & r ⊃ q)) :=
  hs andE₁ taut

end
