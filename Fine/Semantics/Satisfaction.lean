import Fine.Semantics.Model
import Fine.PropositionalLanguage

def satisfies [inst : Model α] (t : α) (f : Form) : Prop :=
  match f with
    | #n => n ∈ inst.valuation t
    | ~f => ∀{p : inst.primes}, t ≤ p → ¬(satisfies (p*).val f)
    | f & g => satisfies t f ∧ satisfies t g
    | f ¦ g => ∀{p : inst.primes}, t ≤ p → satisfies (p*).val f ∨ satisfies (p*).val g
    | Form.impl f g => ∀{u : α}, satisfies u f → satisfies (t ∘ u) g
    --can't pattern match using ⊃ because of collision with set

def psatisfies [inst : Model α] (p : inst.primes) (f : Form) : Prop := satisfies p.val f

infix:128 "⊨"  => satisfies
infix:128 "⊨"  => psatisfies

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
                          have l₁ : s ∘ u ≤ t ∘ u := inst.appMonotoneRight u h₁
                          have l₂ : (s ∘ u) ⊨ g := h₂ h₃
                          exact upwardsClosure l₁ l₂

theorem starCompatRight [inst : Model α] {p : inst.primes} {f : Form} : p* ⊨ f → ¬(p ⊨ ~f) := by
    intro h₁ h₂
    unfold psatisfies at h₂
    unfold satisfies at h₂
    exact h₂ (le_refl p.val) h₁

section

open Classical

theorem nonconstruction {α : Sort u} {p : α → Prop} (h₁ : ¬∀x : α, p x) : (∃x : α, ¬ p x) :=
  by_contradiction λh₂ => 
    have l₁ : ∀x : α, p x := λx : α => by_contradiction λh₃ => h₂ ⟨x, h₃⟩
    h₁ l₁

theorem starCompatLeft [inst : Model α] {p : inst.primes} {f : Form} : ¬(p ⊨ ~f) → p* ⊨ f := by
  intros h₁
  have ⟨x, l₁⟩ := nonconstruction h₁
  have ⟨l₂,l₃⟩ := nonconstruction l₁
  have l₄ := by_contradiction l₃
  have l₅ := inst.starAntitone l₂
  exact upwardsClosure l₅ l₄

end
