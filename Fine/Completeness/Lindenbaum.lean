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
  termination_by lindenbaumSequence _ _ p => (p.fst, p.snd)

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
          
  termination_by lindenbaumSequenceMonotone' _ _ b => (b.fst, b.snd)

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
    have l₃ : lindenbaumSequence t Δ ⟨i,j⟩ ⊆ lindenbaumSequence t Δ ⟨i + 1,Encodable.encode (f,f)⟩ := by
      apply lindenbaumSequenceMonotone
      apply (Prod.Lex.le_iff (i,j) (i + 1,Encodable.encode (f,f))).mpr $ Or.inl $ Nat.lt_succ_self i
    have prf₂ := BProof.monotone (le_trans l₂ l₃) fprf
    have prf₃ : BProof (lindenbaumSequence t Δ ⟨i+1,Encodable.encode (f,f)⟩) (f ¦ f) := BProof.mp prf₂ BTheorem.orI₁
    clear s h₁ l₁ l₂ l₃ fprf prf₁ prf₂ 
    have l₄ : f ∈ lindenbaumSequence t Δ ⟨i + 1, Encodable.encode (f,f) + 1⟩ := by
      unfold lindenbaumSequence
      change
        let prev := lindenbaumSequence t Δ (i + 1, Encodable.encode (f,f));
        let l := (Denumerable.ofNat (Form × Form) (Encodable.encode (f,f))).fst;
        let r := (Denumerable.ofNat (Form × Form) (Encodable.encode (f,f))).snd;
        f ∈ if l¦r ∈ ▲prev then if ▲(prev ∪ {l}) ∩ Δ = ∅ then prev ∪ {l} else prev ∪ {r} else prev
      intros prev l r
      have l₅ : l = f := by 
        change (Denumerable.ofNat (Form × Form) (Encodable.encode (f, f))).fst = f
        rw [Denumerable.ofNat_encode (f,f)]
      have l₆ : r = f := by
        change (Denumerable.ofNat (Form × Form) (Encodable.encode (f, f))).snd = f
        rw [Denumerable.ofNat_encode (f,f)]
      split
      case inl h₂ =>
        split
        . rw [l₅]; exact Or.inr rfl
        . rw [l₆]; exact Or.inr rfl
      case inr h₂ =>
        apply False.elim
        have l₇ : f¦f ∈ ▲prev := ⟨prf₃⟩
        rw [l₅,l₆] at h₂
        exact h₂ l₇
    exact ⟨⟨i + 1, Encodable.encode (f,f) + 1⟩, l₄⟩

theorem lindenbaumIsPrime { t : Th } { Δ : Ctx } : PrimeTheory (lindenbaumExtension t Δ) := by
  intros f g h₁
  have ⟨⟨i,j⟩,h₂⟩ := h₁
  let k := Encodable.encode (f,g)
  have l₁ : lindenbaumSequence t Δ ⟨i,j⟩ ⊆ lindenbaumSequence t Δ ⟨i + 1,k⟩ := by
    apply lindenbaumSequenceMonotone
    apply (Prod.Lex.le_iff (i,j) (i + 1,k)).mpr $ Or.inl $ Nat.lt_succ_self i
  have l₂ : f ¦ g ∈ lindenbaumSequence t Δ ⟨i + 1, k⟩ := l₁ h₂
  clear l₁ h₁ h₂
  have l₃ : f ∈ lindenbaumSequence t Δ ⟨i + 1, k + 1⟩ ∨ g ∈ lindenbaumSequence t Δ ⟨i + 1, k + 1⟩ := by
    unfold lindenbaumSequence
    change
      let prev := lindenbaumSequence t Δ (i + 1, k);
      let l := (Denumerable.ofNat (Form × Form) k).fst;
      let r := (Denumerable.ofNat (Form × Form) k).snd;
      (f ∈ if l¦r ∈ ▲prev then if ▲(prev ∪ {l}) ∩ Δ = ∅ then prev ∪ {l} else prev ∪ {r} else prev) ∨ 
      (g ∈ if l¦r ∈ ▲prev then if ▲(prev ∪ {l}) ∩ Δ = ∅ then prev ∪ {l} else prev ∪ {r} else prev)
    intros prev l r
    have l₄ : Denumerable.ofNat (Form × Form) k = (f,g) := Denumerable.ofNat_encode (f,g)
    have l₅ : l = f := by 
      change (Denumerable.ofNat (Form × Form) k).fst = f
      rw [l₄]
    have l₆ : r = g := by 
      change (Denumerable.ofNat (Form × Form) k).snd = g
      rw [l₄]
    repeat rw [l₅,l₆]
    clear l r l₅ l₆
    cases Classical.em (▲(prev ∪ {f}) ∩ Δ = ∅)
    case' inl h₁ => apply Or.inl
    case' inr h₁ => apply Or.inr
    all_goals
      split
      case inl => exact Or.inr rfl
      case inr h₂ => exact False.elim $ h₂ ⟨BProof.ax l₂⟩
  apply Or.elim l₃
  case left => intros h₁; exact Or.inl ⟨⟨i+1,k+1⟩,h₁⟩
  case right => intros h₁; exact Or.inr ⟨⟨i+1,k+1⟩,h₁⟩

theorem lindenbaumAvoids { t : Th } { Δ : Ctx } { h₁ : ↑t ∩ Δ = ∅ } { h₂ : DisjunctionClosed Δ } : ∀ij, lindenbaumSequence t Δ ij ∩ Δ = ∅ 
  | ⟨0,0⟩ => by exact h₁
  | ⟨i + 1, 0⟩ => by
    change 
      { f : Form | ∃j : Nat, f ∈ lindenbaumSequence t Δ ⟨i, j⟩ } ∩ Δ = ∅
    apply Set.not_nonempty_iff_eq_empty.mp
    intros h₃
    have ⟨w,⟨j,l₂⟩,l₁⟩ := h₃
    clear h₃
    have l₃ := @lindenbaumAvoids t Δ h₁ h₂ ⟨i,j⟩
    exact (Set.not_nonempty_iff_eq_empty.mpr l₃) ⟨w, l₂, l₁⟩
  | ⟨i, j + 1⟩ => by
    apply Set.not_nonempty_iff_eq_empty.mp
    intros h₃
    have ⟨w,l₁,l₂⟩ := h₃
    unfold lindenbaumSequence at l₁
    split at l₁
    case h_1 x heq => injection heq with heq; contradiction
    case h_2 x heq => injection heq with heq; contradiction
    case h_3 x n m heq =>
      injection heq with heq₁ heq₂
      injection heq₂ with heq₂
      rw [←heq₁,←heq₂] at l₁
      clear n m x heq₁ heq₂ h₃
      dsimp at l₁ 
      split at l₁
      case inr h₄ =>
        have l₃ := @lindenbaumAvoids t Δ h₁ h₂ ⟨i,j⟩
        exact (Set.not_nonempty_iff_eq_empty.mpr l₃) ⟨w, l₁, l₂⟩
      case inl h₄ =>
        split at l₁
        all_goals
          cases l₁
          case inl h₆ => 
            have l₃ := @lindenbaumAvoids t Δ h₁ h₂ ⟨i,j⟩
            exact (Set.not_nonempty_iff_eq_empty.mpr l₃) ⟨w, h₆, l₂⟩
          rename_i h₅ h₆
          rw [←h₆] at h₄
        case inl => 
          rw [←h₆] at h₅
          have l₃ : w ∈ ▲(lindenbaumSequence t Δ (i,j) ∪ {w}) := ⟨BProof.ax (Or.inr $ rfl)⟩
          exact Set.not_nonempty_iff_eq_empty.mpr h₅ $ ⟨w,l₃,l₂⟩
        case inr =>
          have l₃ := @lindenbaumAvoids t Δ h₁ h₂ ⟨i,j⟩
          have ⟨x,⟨prf₁⟩,l₅⟩ := Set.nonempty_iff_ne_empty.mpr h₅
          have ⟨prf₂⟩ := h₄
          clear h₄ h₅ h₆
          let k := (Denumerable.ofNat (Form × Form) (j + 0)).fst
          --silly workaround because changeAt doesn't work
          have triv_eq : (Denumerable.ofNat (Form × Form) (j + 0)).fst = k := rfl
          rw [triv_eq] at prf₁
          rw [triv_eq] at prf₂
          clear triv_eq
          have l₆ : x¦w ∈ Δ := h₂ ⟨l₅,l₂⟩
          clear l₂ l₅ h₂
          -- sketch: 
          -- 1. get a theorem t ∧ k → x, for t ⊣ LBS (new general Hilbert-level lemma)
          -- 2. get LBS ⊢ t ∧ k ¦ t ∧ w, by distributivity.
          -- 3. get LBS ⊢ x ¦ w , by or-elim
          -- 4. contradiction via l₃ l₆
          sorry
  termination_by lindenbaumAvoids _ _ _ _ p => (p.fst, p.snd)
