import Fine.Semantics.Model
import Fine.Semantics.Satisfaction
import Fine.Hilbert.SystemB
import Fine.PropositionalLanguage

open Classical

def systemBSoundness (prf: BTheorem f) : valid f := by
  induction prf <;> unfold valid <;> intros α M <;> unfold verifies <;> try apply logicInIdentity.mpr <;> try intros x h₁
  case taut => assumption
  case andE₁ => unfold satisfies at h₁; apply And.left; assumption
  case andE₂ => unfold satisfies at h₁; apply And.right; assumption
  case andI => 
    unfold satisfies at h₁
    unfold satisfies at h₁
    unfold satisfies
    intro u h₂
    apply And.intro
    case left => exact h₁.left h₂
    case right => exact h₁.right h₂
  case orI₁ =>
    unfold satisfies
    intros p h₂
    apply Or.inl
    exact upwardsClosure h₂ h₁
  case orI₂ =>
    unfold satisfies
    intros p h₂
    apply Or.inr
    exact upwardsClosure h₂ h₁
  case orE =>
    unfold satisfies
    intro u h₂
    unfold satisfies at h₂
    apply primeDetermination
    intros p h₃
    rename_i P Q R
    have ⟨q, r, _, c₁,_,c₂⟩ : ∃q r : M.primes, x ≤ q ∧ u ≤ r ∧ (↑q ∘ u) ≤ p ∧ (x ∘ r) ≤ p := M.appBounding x u p h₃
    have l₂ : r ⊨ P ∨ r ⊨ Q := h₂ c₁
    have l₃ : (x ∘ r) ⊨ R := by 
      cases l₂
      case inl => rename_i h₄; exact h₁.1 h₄
      case inr => rename_i h₄; exact h₁.2 h₄
    exact upwardsClosure c₂ l₃
  case dne => 
    apply primeDetermination
    intros p h₂
    unfold satisfies at h₁
    unfold satisfies at h₁
    rename_i P
    have ⟨q, l₁⟩ : ∃q : M.primes, ¬((p*).val ≤ q.val → ¬((q*).val) ⊨ P) := nonconstruction (h₁ h₂)
    have ⟨l₂, l₃⟩ := nonconstruction l₁
    have l₄ := M.starAntitone l₂
    rw [M.starInvolution] at l₄
    exact upwardsClosure l₄ (by_contradiction l₃)
  case dist => 
    unfold satisfies
    intros p h₂
    unfold satisfies at h₁
    have ⟨l₁,l₂⟩ := h₁
    unfold satisfies at l₂
    cases l₂ h₂
    case inl => 
      rename_i _ _ _ h₃
      apply Or.inl
      unfold satisfies
      exact ⟨upwardsClosure h₂ l₁, h₃⟩
    case inr => 
      rename_i _ _ _ h₃
      apply Or.inr
      unfold satisfies
      exact ⟨upwardsClosure h₂ l₁, h₃⟩
  case adj thm₁ thm₂ => 
    unfold satisfies
    exact ⟨thm₁ α M, thm₂ α M⟩
  case mp thm₁ thm₂ => 
    rename_i P Q R S
    have l₁ : M.identity ⊨ P := thm₁ α M
    have l₃ : M.identity ⊨ P ⊃ Q := thm₂ α M
    have l₄ := l₃ l₁
    rw [←M.appLeftIdent M.identity]
    assumption
  case cp thm₁ => 
    rename_i P Q R
    apply primeDetermination
    apply by_contradiction
    intros h₂
    have ⟨q, l₂⟩ := nonconstruction h₂
    have ⟨l₃, l₄⟩ := nonconstruction l₂
    have l₅ := starCompatLeft l₄
    have l₆ : M.identity ⊨ P ⊃ ~Q:= thm₁ α M
    have l₇ : (M.identity ∘ (q*).val) ⊨ ~Q := l₆ l₅
    unfold satisfies at l₇
    have l₈ : ¬(q** ⊨ Q) := by
      rw [M.appLeftIdent (q*).val] at l₇
      exact l₇ (le_refl (q*).val)
    rw [M.starInvolution q] at l₈
    exact l₈ $ upwardsClosure l₃ h₁
  case hs thm₁ thm₂ => 
    rename_i P Q R S
    unfold satisfies
    intros u h₂
    have l₁ := (thm₁ α M) h₂
    rw [M.appLeftIdent u] at l₁
    have l₂ := (thm₂ α M) (h₁ l₁)
    rw [M.appLeftIdent (x ∘ u)] at l₂
    assumption
