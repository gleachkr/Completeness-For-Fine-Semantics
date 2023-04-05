import Fine.Completeness.Lindenbaum

open Classical

def generatedDisjunctions (g : Form) : Set Form
  | f₁ ¦ f₂ => g = f₁ ¦ f₂ ∨ (generatedDisjunctions g f₁ ∧ generatedDisjunctions g f₂)
  | y => g = y

theorem primeAnalysis : ∀t : Th, t.val = Set.interₛ { p | isPrimeTheory p ∧ t.val ≤ p } := by
  intros t
  ext x
  apply Iff.intro
  case h.mp =>
    intros h₁
    apply Set.mem_interₛ.mpr
    intros r h₂
    exact h₂.right h₁
  case h.mpr =>
    intros h₁
    apply byContradiction
    intros h₂
    have l₁ : ∀ g : Form, g ∈ generatedDisjunctions x → {g} ⊢ x := by
      intros g h₃
      induction g
      case or f g ih₁ ih₂ =>
        cases h₃
        case inl h₄ => rw [h₄]; exact ⟨BProof.ax rfl⟩
        case inr h₄ =>
          have ⟨prf₁⟩ := ih₁ h₄.left
          have ⟨prf₂⟩ := ih₂ h₄.right
          have thm₁ := BTheorem.mp (BTheorem.adj (BTheorem.fromProof prf₁) (BTheorem.fromProof prf₂)) BTheorem.orE
          exact ⟨BTheorem.toProof thm₁⟩
      all_goals
        cases h₃; exact ⟨BProof.ax rfl⟩
    have l₂ : ↑t ∩ generatedDisjunctions x = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intros y h₃
      have ⟨prf₁⟩ := l₁ y h₃.right
      exact h₂ (t.property.mpr ⟨BProof.monotone (Set.singleton_subset_iff.mpr h₃.left) prf₁⟩)
    have l₃ : isDisjunctionClosed (generatedDisjunctions x) := by
      intros f g h₃
      exact Or.inr h₃
    have l₄ : x ∈ generatedDisjunctions x := by 
      cases x
      case or f g => exact Or.inl rfl
      all_goals 
        exact rfl
    have l₅ := lindenbaumTheorem l₂ l₃
    have l₆ := (Set.mem_interₛ.mp h₁) 
      (lindenbaumExtension t (generatedDisjunctions x)) 
      ⟨lindenbaumIsPrime, lindenbaumExtensionExtends⟩
    exact Set.eq_empty_iff_forall_not_mem.mp l₅ x ⟨l₆,l₄⟩
