import Mathlib.Data.Finset.Basic
import Mathlib.Init.Set

lemma finiteExhaustion [instDec: DecidableEq α] [LinearOrder β] [Inhabited β] {fam : β → Set α} {fin : Finset α} :
  Monotone fam → ↑fin ⊆ {x : α | ∃n : β, x ∈ fam n } → ∃n : β, ↑fin ⊆ fam n := by
    intros h₁
    apply @Finset.induction_on α (λfs => ↑fs ⊆ {x : α | ∃n : β, x ∈ fam n } → ∃n : β, ↑fs ⊆ fam n) instDec fin
    case empty =>
      intros _
      refine ⟨default,?_⟩
      intros h₂ h₃
      contradiction
    case insert => 
      intros x fs _ h₃ h₄
      have l₁ : x ∈ {x : α | ∃n : β, x ∈ fam n } := h₄ $ Finset.mem_insert_self x fs
      have ⟨n, l₂⟩ := l₁
      have l₃ : ↑fs ⊆ {x : α | ∃n : β, x ∈ fam n } := by
        intros y h₅
        exact h₄ $ Finset.mem_insert_of_mem (Finset.mem_coe.mp h₅)
      have ⟨m, l₄⟩ := h₃ l₃
      cases le_total n m
      case inl leqthan => 
        have l₅ := (h₁ leqthan) l₂
        refine ⟨m,?_⟩
        intros y h₄
        cases Finset.mem_insert.mp h₄
        case inl h₅ => rw [h₅]; assumption
        case inr h₅ => exact l₄ h₅
      case inr geqthan =>
        have l₅ := le_trans l₄ (h₁ geqthan) 
        refine ⟨n,?_⟩
        intros y h₄
        cases Finset.mem_insert.mp h₄
        case inl h₅ => rw [h₅]; assumption
        case inr h₅ => exact l₅ h₅
