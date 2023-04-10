import Fine.Completeness.Lindenbaum

open Classical

def generatedDisjunctions (g : Form) : Set Form
  | f₁ ¦ f₂ => g = f₁ ¦ f₂ ∨ (generatedDisjunctions g f₁ ∧ generatedDisjunctions g f₂)
  | y => g = y

theorem primeAnalysis : ∀t : Th, t.val = Set.interₛ { p | isPrimeTheory p ∧ t ≤ p ∧ formalTheory p } := by
  intros t
  ext x
  apply Iff.intro
  case h.mp =>
    intros h₁
    apply Set.mem_interₛ.mpr
    intros r h₂
    exact h₂.right.left h₁
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
      ⟨lindenbaumIsPrime, lindenbaumExtensionExtends, lindenbaumIsFormal⟩
    exact Set.eq_empty_iff_forall_not_mem.mp l₅ x ⟨l₆,l₄⟩

theorem appBoundingFormalApplication : ∀t u : Th, ∀p : Pr, formalApplicationFunction t u ≤ p →
  ∃q r: Pr, t ≤ q ∧ u ≤ r ∧ formalApplicationFunction q u ≤ p ∧ formalApplicationFunction t r ≤ p := by
    intros t u p h₁
    have ⟨q,h₂,h₃⟩ := lemma1 t u p h₁
    have ⟨r,h₄,h₅⟩ := lemma2 t u p h₁
    exact ⟨q,r,h₂,h₄,h₃,h₅⟩

  where 
    lemma1 : ∀t u : Th, ∀p :Pr, formalApplicationFunction t u ≤ p → ∃ q : Pr, t ≤ q ∧ formalApplication q u ⊆ p := by
      intros t u p h₁
      let Δ := {f : Form | ¬(formalApplication (▲{f}) u ⊆ p) }
      have l₂ : ↑t ∩ Δ = ∅ := by
        apply Set.eq_empty_iff_forall_not_mem.mpr
        intros P h₂
        have l₃ : ▲{P} ⊆ ↑t := generatedContained (Set.singleton_subset_iff.mpr h₂.left)
        have l₄ := formalAppMonotoneRight ↑u l₃
        exact h₂.right $ le_trans l₄ h₁
      have l₃ : isDisjunctionClosed Δ := by
        intros P Q h₁ h₂
        have ⟨R,l₄⟩ := nonconstruction h₁.left
        have ⟨⟨S,l₆,⟨prf₁⟩⟩,l₈⟩ := nonconstruction l₄
        have ⟨T,l₉⟩ := nonconstruction h₁.right
        have ⟨⟨U,l₁₀,⟨prf₂⟩⟩,l₁₂⟩ := nonconstruction l₉
        clear h₁ l₄ l₉
        have l₁₃ : ¬(R¦T ∈ p) := λw => Or.elim (p.property w) l₈ l₁₂
        apply l₁₃
        apply h₂
        clear l₈ l₁₂ l₁₃ h₂
        have prf₃ : BProof {P} (S & U ⊃ R ¦ T) := BProof.mp 
          (BProof.mp prf₁ (BTheorem.hs BTheorem.taut BTheorem.orI₁))
          (BTheorem.hs BTheorem.andE₁ BTheorem.taut)
        have prf₄ : BProof {Q} (S & U ⊃ R ¦ T) := BProof.mp 
          (BProof.mp prf₂ (BTheorem.hs BTheorem.taut BTheorem.orI₂))
          (BTheorem.hs BTheorem.andE₂ BTheorem.taut)
        have prf₅ : BProof {P ¦ Q} (S & U ⊃ R ¦ T) := BTheorem.toProof $
          BTheorem.mp (BTheorem.adj (BTheorem.fromProof prf₃) (BTheorem.fromProof prf₄)) BTheorem.orE
        clear prf₁ prf₂ prf₃ prf₄
        have l₁₄ : S & U ∈ u := u.property.mpr ⟨BProof.adj (BProof.ax l₆) (BProof.ax l₁₀)⟩
        exact ⟨S & U, l₁₄, ⟨prf₅⟩⟩
      have l₄ : lindenbaumExtension t Δ ∩ Δ = ∅  := lindenbaumTheorem l₂ l₃
      clear l₂ l₃
      refine ⟨⟨⟨lindenbaumExtension t Δ, lindenbaumIsFormal⟩, lindenbaumIsPrime⟩, lindenbaumExtensionExtends, ?_⟩
      change formalApplication (lindenbaumExtension t Δ) ↑u ⊆ p
      intros P h₁
      have ⟨Q,h₂,h₃⟩ := h₁
      have l₄ : formalApplication (▲{Q⊃P}) ↑u ⊆ ↑↑p := by
        apply byContradiction
        intros h₄
        exact (Set.eq_empty_iff_forall_not_mem.mp l₄) (Q⊃P) ⟨h₃,h₄⟩
      exact l₄ ⟨Q,h₂,⟨BProof.ax rfl⟩⟩

    lemma2 : ∀t u : Th, ∀p :Pr, formalApplicationFunction t u ≤ p → ∃ r : Pr, u ≤ r ∧ formalApplication t r ⊆ p := by
      intros t u p h₁
      let Δ := {f : Form | ¬(formalApplication t (▲{f}) ⊆ p) }
      have l₂ : ↑u ∩ Δ = ∅ := by
        apply Set.eq_empty_iff_forall_not_mem.mpr
        intros P h₂
        have l₃ : ▲{P} ⊆ ↑u := generatedContained (Set.singleton_subset_iff.mpr h₂.left)
        have l₄ := formalAppMonotoneLeft ↑t l₃
        exact h₂.right $ le_trans l₄ h₁
      have l₃ : isDisjunctionClosed Δ := by
        intros P Q h₁ h₂
        have ⟨R,l₄⟩ := nonconstruction h₁.left
        have ⟨⟨S,⟨prf₁⟩,l₆⟩,l₈⟩ := nonconstruction l₄
        have ⟨T,l₉⟩ := nonconstruction h₁.right
        have ⟨⟨U,⟨prf₂⟩,l₁₀⟩,l₁₂⟩ := nonconstruction l₉
        clear h₁ l₄ l₉
        have l₁₃ : ¬(R¦T ∈ p) := λw => Or.elim (p.property w) l₈ l₁₂
        apply l₁₃
        apply h₂
        clear l₈ l₁₂ l₁₃ h₂
        have l₁₄ : S¦U ∈ ▲{P¦Q} := ⟨BTheorem.toProof (BTheorem.orFunctor (BTheorem.fromProof prf₁) (BTheorem.fromProof prf₂))⟩
        have l₁₅ : (S¦U ⊃ R¦T) ∈ t := t.property.mpr ⟨BProof.mp (BProof.adj 
          (BProof.mp (BProof.ax l₆) (BTheorem.hs BTheorem.taut BTheorem.orI₁))
          (BProof.mp (BProof.ax l₁₀) (BTheorem.hs BTheorem.taut BTheorem.orI₂)))
          BTheorem.orE⟩
        exact ⟨S ¦ U, l₁₄, l₁₅⟩
      have l₄ : lindenbaumExtension u Δ ∩ Δ = ∅  := lindenbaumTheorem l₂ l₃
      clear l₂ l₃
      refine ⟨⟨⟨lindenbaumExtension u Δ, lindenbaumIsFormal⟩, lindenbaumIsPrime⟩, lindenbaumExtensionExtends, ?_⟩
      change formalApplication ↑t (lindenbaumExtension u Δ) ⊆ p
      intros P h₁
      have ⟨Q,h₂,h₃⟩ := h₁
      have l₄ : formalApplication ↑t (▲{Q}) ⊆ ↑↑p := by
        apply byContradiction
        intros h₄
        exact (Set.eq_empty_iff_forall_not_mem.mp l₄) Q ⟨h₂,h₄⟩
      exact l₄ ⟨Q,⟨BProof.ax rfl⟩,h₃⟩

def theoryValuation : Th → Set Nat := λt => { n | #n ∈ t }

theorem theoryValuationMonotone : Monotone theoryValuation := by
  intros _ _ h₁ n h₂
  exact h₁ h₂

theorem theoryValuationBounding : ∀t : Th, ∀x : Nat, (∀p : Pr, t ≤ p → x ∈ theoryValuation p) → x ∈ theoryValuation t := by
  intros t x h₁
  change #x ∈ t.val
  rw [primeAnalysis t]
  apply Set.mem_interₛ.mpr
  intros r h₂
  exact h₁ ⟨⟨r,h₂.right.right⟩,h₂.left⟩ h₂.right.left

instance canonicalInstance : Model Th where
  prime := { x | isPrimeTheory x }
  application := formalApplicationFunction
  routeleyStar := primeStarFunction
  valuation := theoryValuation
  identity := BTh
  appMonotoneLeft := formalAppFunctionMonotoneLeft
  appMonotoneRight := formalAppFunctionMonotoneRight
  appBounding := appBoundingFormalApplication
  appLeftIdent := formalAppIdentLeft
  valMonotone := theoryValuationMonotone
  valBounding := theoryValuationBounding
  starAntitone := starAntitone
  starInvolution := starInvolution

theorem canonicalSatisfaction : ∀{t : Th}, ∀{f : Form}, t ⊨ f ↔ f ∈ t.val := by
  intros t f
  cases f
  all_goals apply Iff.intro <;> intros h₁
  case atom.mp => exact h₁
  case atom.mpr => exact h₁
  case and.mp f g => 
      have l₁ : f ∈ t := canonicalSatisfaction.mp h₁.left
      have l₂ : g ∈ t := canonicalSatisfaction.mp h₁.right
      exact t.property.mpr ⟨BProof.adj (BProof.ax l₁) (BProof.ax l₂)⟩
  case and.mpr f g =>
      have l₁ : t ⊨ f := canonicalSatisfaction.mpr $ t.property.mpr ⟨BProof.mp (BProof.ax h₁) BTheorem.andE₁⟩
      have l₂ : t ⊨ g := canonicalSatisfaction.mpr $ t.property.mpr ⟨BProof.mp (BProof.ax h₁) BTheorem.andE₂⟩
      exact ⟨l₁,l₂⟩
  case or.mp f g =>
    rw [primeAnalysis]
    intros p h₂
    let pr : Pr := ⟨⟨p, h₂.right.right⟩,h₂.left⟩
    have l₁ := @h₁ pr h₂.right.left
    cases l₁
    case inl h₃ => 
      have l₂ := canonicalSatisfaction.mp h₃
      exact h₂.right.right.mpr ⟨BProof.mp (BProof.ax l₂) BTheorem.orI₁⟩
    case inr h₃ => 
      have l₂ := canonicalSatisfaction.mp h₃
      exact h₂.right.right.mpr ⟨BProof.mp (BProof.ax l₂) BTheorem.orI₂⟩
  case or.mpr f g =>
    intros p h₂
    rw [primeAnalysis] at h₁
    have l₁ : f ¦ g ∈ p.val.val := (Set.mem_interₛ.mp h₁ p) ⟨p.property, h₂, p.val.property⟩
    have l₂ : f ∈ p.val.val ∨ g ∈ p.val.val := p.property l₁
    cases l₂
    case inl h₂ => exact Or.inl $ canonicalSatisfaction.mpr h₂
    case inr h₂ => exact Or.inr $ canonicalSatisfaction.mpr h₂
  case neg.mp f => 
    rw [primeAnalysis]
    intros p h₂
    let pr : Pr := ⟨⟨p, h₂.right.right⟩,h₂.left⟩
    have l₁ := @h₁ pr h₂.right.left
    have l₂ := l₁ ∘ canonicalSatisfaction.mpr 
    apply byContradiction
    exact l₂
  case neg.mpr f => 
    intros p h₂ h₃
    rw [primeAnalysis] at h₁
    have l₁ : ~f ∈ p.val.val := (Set.mem_interₛ.mp h₁ p) ⟨p.property, h₂, p.val.property⟩
    exact canonicalSatisfaction.mp h₃ l₁
  case impl.mp f g =>
    apply byContradiction
    intros h₂
    let Δ : Th := ⟨▲{f}, generatedFormal {f}⟩
    have l₁ : ¬(g ∈ (formalApplicationFunction t Δ).val) := by
      intros h₃
      have ⟨q,⟨prf₁⟩,l₂⟩ := h₃
      have ⟨prf₂⟩ := t.property.mp l₂
      have prf₃ := BProof.mp prf₂ (BTheorem.hs (BTheorem.fromProof prf₁) BTheorem.taut)
      exact h₂ $ t.property.mpr ⟨prf₃⟩
    have l₂ : Δ ⊨ f := canonicalSatisfaction.mpr ⟨BProof.ax rfl⟩
    exact l₁ $ canonicalSatisfaction.mp (h₁ l₂)
  case impl.mpr f g => 
    intros r h₂
    have l₁ := canonicalSatisfaction.mp h₂
    have l₂ : g ∈ (formalApplicationFunction t r).val := ⟨f, l₁, h₁⟩
    exact canonicalSatisfaction.mpr l₂

theorem systemBCompleteness (h₁ : valid f) : Nonempty (BTheorem f) :=
  canonicalSatisfaction.mp $ h₁ Th
