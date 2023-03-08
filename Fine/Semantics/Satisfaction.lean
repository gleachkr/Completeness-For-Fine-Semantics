import Fine.Semantics.Model
import Fine.PropositionalLanguage

def satisfies [inst : Model α] (t : α) (f : Form) : Prop :=
  match f with
    | #n => n ∈ inst.valuation t
    | ~f => ∀{p : inst.primes}, t ≤ p → ¬(satisfies (p*).val f)
    | f & g => satisfies t f ∧ satisfies t g
    | f ¦ g => ∀{p : inst.primes}, t ≤ p → satisfies p.val f ∨ satisfies p.val g
    | Form.impl f g => ∀{u : α}, satisfies u f → satisfies (t ∙ u) g
    --can't pattern match using ⊃ because of collision with set

abbrev psatisfies [inst : Model α] (p : inst.primes) (f : Form) : Prop := satisfies p.val f

infix:128 "⊨"  => psatisfies
infix:128 "⊨"  => satisfies

abbrev verifies (inst : Model α) (f : Form) : Prop := inst.identity ⊨ f

abbrev valid (f : Form) : Prop := ∀α : Type, ∀m : Model α, verifies m f

theorem upwardsClosure [inst : Model α] {s t : α} {f : Form} (h₁: s ≤ t) (h₂ : s ⊨ f) : t ⊨ f := 
  match f with
    | #n => have l₁ : inst.valuation s ⊆ inst.valuation t := inst.valMonotone s t h₁
            l₁ h₂
    | ~g => by unfold satisfies
               intros p h₃ h₄
               exact h₂ (le_trans h₁ h₃) h₄
    | f & g => by unfold satisfies
                  apply And.intro
                  case left => exact upwardsClosure h₁ h₂.left
                  case right => exact upwardsClosure h₁ h₂.right
    | f ¦ g => by unfold satisfies
                  intros p h₃
                  apply Or.elim (h₂ (le_trans' h₃ h₁))
                  case left => intro h₄; exact Or.inl h₄
                  case right => intro h₄; exact Or.inr h₄
    | Form.impl f g => by unfold satisfies
                          intros u h₃
                          have l₁ : s ∙ u ≤ t ∙ u := inst.appMonotoneRight u h₁
                          have l₂ : (s ∙ u) ⊨ g := h₂ h₃
                          exact upwardsClosure l₁ l₂

theorem primeDetermination [inst : Model α] {t : α} { f : Form } (h₁ : ∀p : inst.primes, t ≤ p → p ⊨ f) : t ⊨ f := 
  match f with
    | #n => Model.valBounding t n h₁
    | ~f => by unfold satisfies
               intros p h₂ h₃
               exact h₁ p h₂ (le_refl p.val) h₃
    | f & g => by unfold satisfies
                  apply And.intro
                  case left => 
                    have l₁ : ∀p : inst.primes, t ≤ p → p ⊨ f := by
                      intros p h₂
                      exact (h₁ p h₂).left
                    exact primeDetermination l₁
                  case right =>
                    have l₁ : ∀p : inst.primes, t ≤ p → p ⊨ g := by
                      intros p h₂
                      exact (h₁ p h₂).right
                    exact primeDetermination l₁
    | f ¦ g => by unfold satisfies
                  intros p h₂
                  cases h₁ p h₂ (le_refl p.val)
                  case inl => 
                    apply Or.inl
                    assumption
                  case inr => 
                    apply Or.inr
                    assumption
    | Form.impl f g => by unfold satisfies
                          intros u h₂
                          apply primeDetermination
                          intros p h₃
                          have ⟨q, _, l₃,_,l₄,_⟩ : ∃q r : inst.primes, t ≤ q ∧ u ≤ r ∧ (↑q ∙ u) ≤ p ∧ (t ∙ r) ≤ p.val := inst.appBounding t u p h₃
                          have l₅ : (↑q ∙ u) ⊨ g  := h₁ q l₃ h₂
                          exact upwardsClosure l₄ l₅

theorem starCompatRight [inst : Model α] {p : inst.primes} {f : Form} : p* ⊨ f → ¬(p ⊨ ~f) := by
    intro h₁ h₂
    unfold psatisfies at h₂
    unfold satisfies at h₂
    exact h₂ (le_refl p.val) h₁

theorem logicInIdentity [inst : Model α] {f g : Form} : inst.identity ⊨ f ⊃ g ↔ ∀x : α, x ⊨ f → x ⊨ g := by
  apply Iff.intro
  case mp => 
    intros h₁ x h₂
    have l₁ : (inst.identity ∙ x) ⊨ g := h₁ h₂
    rw [←inst.appLeftIdent x]
    assumption
  case mpr =>
    intro h₁
    unfold satisfies
    intro u h₂
    rw [inst.appLeftIdent u]
    exact h₁ u h₂

section

open Classical

theorem nonconstruction {α : Sort u} {p : α → Prop} (h₁ : ¬∀x : α, p x) : (∃x : α, ¬ p x) :=
  byContradiction λh₂ => 
    have l₁ : ∀x : α, p x := λx : α => byContradiction λh₃ => h₂ ⟨x, h₃⟩
    h₁ l₁

theorem starCompatLeft [inst : Model α] {p : inst.primes} {f : Form} : ¬(p ⊨ ~f) → p* ⊨ f := by
  intros h₁
  have ⟨x, l₁⟩ := nonconstruction h₁
  have ⟨l₂,l₃⟩ := nonconstruction l₁
  have l₄ := byContradiction l₃
  have l₅ := inst.starAntitone l₂
  exact upwardsClosure l₅ l₄

end
