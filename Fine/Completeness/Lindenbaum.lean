import Fine.FormalTheories
import Mathlib.Data.Prod.Lex
import Fine.Util.util

open Classical

def lindenbaumSequence (t : Th) (Δ : Ctx) : Lex (Nat × Nat) → Ctx
  | ⟨0, 0⟩ => t.val
  | ⟨i + 1, 0⟩ => { f : Form | ∃j : Nat, f ∈ lindenbaumSequence t Δ ⟨i, j⟩ }
  | ⟨i, j + 1⟩ => 
    let prev := lindenbaumSequence t Δ ⟨i, j⟩
    let l := (Denumerable.ofNat (Form × Form) j).fst
    let r := (Denumerable.ofNat (Form × Form) j).snd
    if l ¦ r ∈ ▲prev
    then if ▲(prev ∪ {l}) ∩ Δ = ∅
      then prev ∪ {l}
      else prev ∪ {r}
    else prev
  termination_by lindenbaumSequence t Δ p => (p.fst, p.snd)


lemma lindenbaumSequenceMonotone' { t : Th } { Δ : Ctx } : ∀b a, a ≤ b → lindenbaumSequence t Δ a ⊆ lindenbaumSequence t Δ b := by
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
        have l₄ := @lindenbaumSequenceMonotone' t Δ (i,b₁) (a₁, b₁) l₃
        apply le_trans l₄
        intros f h₂
        exact ⟨b₁,h₂⟩
      case right b₁ h₂ =>
        rw [Nat.le_zero_eq b₁] at h₂
        rw [h₂]
    | ⟨i, j + 1⟩ =>
      have lem : lindenbaumSequence t Δ (i, j) ≤ lindenbaumSequence t Δ (i, j + 1) := by
        intros f h₃
        unfold lindenbaumSequence
        split
        case h_1 _ heq | h_2 _ heq => injection heq; contradiction
        case h_3 i' j' heq =>
          injection heq with heq₁ heq₂
          injection heq₂ with heq₂
          have heq₃ : j = j' := heq₂
          rw [←heq₁, ←heq₃]
          change
            let prev := lindenbaumSequence t Δ (i, j);
            let l := (Denumerable.ofNat (Form × Form) j).fst;
            let r := (Denumerable.ofNat (Form × Form) j).snd;
            f ∈ if l¦r ∈ ▲prev then if ▲(prev ∪ {l}) ∩ Δ = ∅ then prev ∪ {l} else prev ∪ {r} else prev
          intros prev l r
          split
          case inl =>
            split
            case inl | inr => apply Or.inl h₃
          case inr => exact h₃
      intros a h₁
      cases h₁
      case left a₁ b₁ h₂ =>
          have l₁ : a₁ < i ∨ a₁ = i ∧ b₁ ≤ j := Or.inl h₂
          have l₂ := (Prod.Lex.le_iff (a₁, b₁) (i,j)).mpr l₁
          have l₃ := @lindenbaumSequenceMonotone' t Δ (i,j) (a₁, b₁)  l₂
          apply le_trans l₃
          exact lem
      case right b₁ h₂ =>
        cases h₂
        case refl => intros _ h₁; assumption
        case step h₂ =>
          have l₁ : i < i ∨ i = i ∧ b₁ ≤ j := Or.inr ⟨rfl, h₂⟩
          have l₂ := (Prod.Lex.le_iff (i, b₁) (i,j)).mpr l₁
          have l₃ := @lindenbaumSequenceMonotone' t Δ (i,j) (i, b₁)  l₂
          apply le_trans l₃
          exact lem
          
  termination_by lindenbaumSequenceMonotone' t Δ b => (b.fst, b.snd)

lemma lindenbaumSequenceMonotone { t : Th } { Δ : Ctx } : Monotone (lindenbaumSequence t Δ) := by
  intros a b
  exact lindenbaumSequenceMonotone' b a  

def lindenbaumExtension (t : Th) (Δ : Ctx) : Ctx := {f | ∃ij : Nat × Nat, f ∈ lindenbaumSequence t Δ ij }

lemma lindenbaumExtensionExtends { t : Th } { Δ : Ctx } : t.val ⊆ lindenbaumExtension t Δ := by
  intros f h₁
  refine ⟨⟨0,0⟩,?_⟩
  assumption

theorem lindenbaumIsFormal { t : Th } { Δ : Ctx } : formalTheory (lindenbaumExtension t Δ) := by
  intros f
  apply Iff.intro
  case mp =>
    intro h₁
    exact ⟨BProof.ax h₁⟩
  case mpr =>
    intro h₁
    have ⟨prf₁⟩ := h₁
    have ⟨s, l₁, fprf⟩ := BProof.compactness prf₁
    have ⟨⟨i,j⟩,l₂⟩ := finiteExhaustion lindenbaumSequenceMonotone l₁
    have l₃ : lindenbaumSequence t Δ ⟨i,j⟩ ⊆ lindenbaumSequence t Δ ⟨i+1,0⟩ := by
      apply lindenbaumSequenceMonotone
      apply (Prod.Lex.le_iff (i,j) (i+1,0)).mpr
      exact Or.inl $ Nat.succ_eq_add_one i ▸ Nat.lt_succ_self i
    have l₄ : ↑s ⊆ lindenbaumSequence t Δ ⟨i+1,0⟩ := by
      intros g h₂
      exact l₃ (l₂ h₂)
    clear l₁ l₂ l₃
    have prf₂ : BProof (lindenbaumSequence t Δ ⟨i+1,0⟩) f := BProof.monotone l₄ fprf
    clear fprf l₄
    sorry
      


