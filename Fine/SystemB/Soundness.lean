import Fine.Semantics.Model
import Fine.Semantics.Satisfaction
import Fine.SystemB.Hilbert
import Fine.PropositionalLanguage

open Classical

def systemBSoundness (prf: BTheorem f) : valid f := by
  induction prf <;> unfold valid <;> intros α M <;> unfold verifies <;> try apply logicInIdentity.mpr <;> try intros x h₁
  case taut => assumption
  case andE₁ => unfold satisfies at h₁; apply And.left; assumption
  case andE₂ => unfold satisfies at h₁; apply And.right; assumption
  case andI => 
    intro u h₂
    apply And.intro
    case left => exact h₁.left h₂
    case right => exact h₁.right h₂
  case orI₁ =>
    intros p h₂
    apply Or.inl
    exact upwardsClosure h₂ h₁
  case orI₂ =>
    intros p h₂
    apply Or.inr
    exact upwardsClosure h₂ h₁
  case orE P Q R=>
    intro u h₂
    apply primeDetermination
    intros p h₃
    have ⟨_, r, _, c₁,_,c₂⟩ : ∃q r : M.primes, x ≤ q ∧ u ≤ r ∧ (↑q ∙ u) ≤ p ∧ (x ∙ r) ≤ p := M.appBounding x u p h₃
    have l₂ : r ⊨ P ∨ r ⊨ Q := h₂ c₁
    have l₃ : (x ∙ r) ⊨ R := by 
      cases l₂
      case inl h₄ => exact h₁.1 h₄
      case inr h₄ => exact h₁.2 h₄
    exact upwardsClosure c₂ l₃
  case dne P => 
    apply primeDetermination
    intros p h₂
    have ⟨q, l₁⟩ : ∃q : M.primes, ¬(p* ≤ q → ¬(q*) ⊨ P) := nonconstruction (h₁ h₂)
    have ⟨l₂, l₃⟩ := nonconstruction l₁
    have l₄ := M.starAntitone l₂
    rw [M.starInvolution] at l₄
    exact upwardsClosure l₄ (byContradiction l₃)
  case dist => 
    intros p h₂
    have ⟨l₁,l₂⟩ := h₁
    cases l₂ h₂
    case inl h₃ => exact Or.inl ⟨upwardsClosure h₂ l₁, h₃⟩
    case inr h₃ => exact Or.inr ⟨upwardsClosure h₂ l₁, h₃⟩
  case adj val₁ val₂ => exact ⟨val₁ α, val₂ α⟩
  case mp P Q _ _ val₁ val₂ => 
    have l₁ : M.identity ⊨ P := val₁ α
    have l₃ : M.identity ⊨ P ⊃ Q := val₂ α
    have l₄ := l₃ l₁
    rw [←M.appLeftIdent M.identity]
    assumption
  case cp P Q _ val₁ => 
    apply primeDetermination
    apply byContradiction
    intros h₂
    have ⟨q, l₂⟩ := nonconstruction h₂
    have ⟨l₃, l₄⟩ := nonconstruction l₂
    have l₅ := starCompatLeft l₄
    have l₆ : M.identity ⊨ P ⊃ ~Q:= val₁ α
    have l₇ : (M.identity ∙ (q*)) ⊨ ~Q := l₆ l₅
    have l₈ : ¬(q** ⊨ Q) := by
      rw [M.appLeftIdent (q*)] at l₇
      exact l₇ (le_refl (q*))
    rw [M.starInvolution q] at l₈
    exact l₈ $ upwardsClosure l₃ h₁
  case hs val₁ val₂ => 
    intros u h₂
    have l₁ := (val₁ α) h₂
    rw [M.appLeftIdent u] at l₁
    have l₂ := (val₂ α) (h₁ l₁)
    rw [M.appLeftIdent (x ∙ u)] at l₂
    assumption
