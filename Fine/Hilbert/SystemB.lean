import Fine.PropositionalLanguage

inductive BTheorem : Form → Prop
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

inductive BProof : Ctx → Form → Prop
  | ax {Γ} {p} (h: p ∈ Γ) : BProof Γ p
  | mp {Γ} {p} {q} (h₁ : BTheorem p) (h₂ : BProof Γ (p ⊃ q)) : BProof Γ q
  | adj {Γ} {p} {q} (h₁ : BProof Γ p) (h₂ : BProof Γ q) : BProof Γ (p & q)

section

open BTheorem

variable {p q r s : Form} 

theorem BTheorem.demorgansLaw : BTheorem ((p & q) ⊃ ~(~p ¦ ~q)) := 
  have l₁ : ∀{r : Form}, BTheorem (r ⊃ ~~r) := cp taut
  have l₂ : BTheorem (~p ⊃ ~(p & q)) := cp $ mp taut (hs andE₁ l₁)
  have l₃ : BTheorem (~q ⊃ ~(p & q)) := cp $ mp taut (hs andE₂ l₁)
  cp $ mp (adj l₂ l₃) orE

theorem BTheorem.transitivity (h₁ : BTheorem (p ⊃ q)) (h₂ : BTheorem (q ⊃ r)) : BTheorem (p ⊃ r) :=
  mp taut (hs h₁ h₂) 

example : BTheorem ((p ⊃ q) ⊃ (p ⊃ (q ¦ r))) :=
  hs taut orI₁

example : BTheorem ((p ⊃ q) ⊃ (p & r ⊃ q)) :=
  hs andE₁ taut

end
