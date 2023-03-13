import Fine.FormalTheories
import Mathlib.Data.Prod.Lex

open Classical

def lindenbaumSequence (t : Th) (Δ : Ctx) : Lex (Nat × Nat) → Ctx
  | ⟨0, 0⟩ => t.val
  | ⟨i + 1, 0⟩ => { f : Form | ∃j : Nat, f ∈ lindenbaumSequence t Δ ⟨i, j⟩ }
  | ⟨i, j + 1⟩ => 
    have prev := lindenbaumSequence t Δ ⟨i, j⟩
    have ⟨l,r⟩ := Denumerable.ofNat (Form × Form) j
    if l ¦ r ∈ ▲prev 
    then if ▲(prev ∪ {l}) ∩ Δ = ∅
      then prev ∪ {l}
      else prev ∪ {r}
    else prev
  termination_by lindenbaumSequence t Δ p => (p.fst, p.snd)

lemma lindenbaumSequenceMonotone { t : Th } { Δ : Ctx } : ∀b a, a ≤ b → lindenbaumSequence t Δ a ⊆ lindenbaumSequence t Δ b := by
  intros b
  match b with
    | ⟨0, 0⟩ => 
      intros a h₁
      cases h₁
      case left a₁ _ h₂ => exact False.elim $ Nat.not_lt_zero a₁ h₂
      case right b₁ h₂ =>
        rw [Nat.le_zero_eq b₁] at h₂
        rw [h₂]
    | ⟨i + 1, 0⟩ => 
      intros a h₁
      cases h₁
      case left a₁ b₁ h₂ => 
        have l₁ : a₁ < i ∨ a₁ = i := Nat.lt_or_eq_of_le $ Nat.lt_succ.mp h₂
        have l₂ : a₁ < i ∨ a₁ = i ∧ b₁ ≤ b₁ := by 
          cases l₁
          case inl h₂ => exact Or.inl h₂
          case inr h₂ => exact Or.inr ⟨h₂, le_refl b₁⟩
        have l₃ := (Prod.Lex.le_iff (a₁, b₁) (i,b₁)).mpr l₂
        have l₄ := @lindenbaumSequenceMonotone t Δ (i,b₁) (a₁, b₁) l₃
        apply le_trans l₄
        intros f h₂
        exact ⟨b₁,h₂⟩
      case right b₁ h₂ => 
        rw [Nat.le_zero_eq b₁] at h₂
        rw [h₂]
    | ⟨i, j + 1⟩ => 
      intros a h₁
      cases h₁
      case left a₁ b₁ h₂ => sorry
      case right b₁ h₂ => 
        cases h₂
        case refl => intros f h₁; assumption
        case step h₂ => 
          have l₁ : i < i ∨ i = i ∧ b₁ ≤ j := Or.inr ⟨rfl, h₂⟩
          have l₂ := (Prod.Lex.le_iff (i, b₁) (i,j)).mpr l₁
          have l₃ := @lindenbaumSequenceMonotone t Δ (i,j) (i, b₁)  l₂
          apply le_trans l₃
          intros f h₃
          sorry

          
  termination_by lindenbaumSequenceMonotone t Δ b => (b.fst, b.snd)

def lindenbaumExtension (t : Th) (Δ : Ctx) : Ctx := {f | ∃n m : Nat, f ∈ lindenbaumSequence t Δ ⟨n, m⟩ }

lemma lindenbaumExtensionExtends { t : Th } { Δ : Ctx } : t.val ⊆ lindenbaumExtension t Δ := by
  intros f h₁
  refine ⟨0,0,?_⟩
  assumption

theorem lindenbaumIsFormal { t : Th } { Δ : Ctx } : formalTheory (lindenbaumExtension t Δ) := sorry
