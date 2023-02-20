import Fine.Semantics.Model
import Fine.PropositionalLanguage

def satisfies [inst : Model α] (t : α) (f : Form) : Prop :=
  match f with
    | #n => n ∈ inst.valuation t
    | ~f => ∀{p : α}, ∀h : p ∈ inst.prime, t ≤ p → ¬(satisfies (⟨p,h⟩*).val f)
    | f & g => satisfies t f ∧ satisfies t g
    | f ¦ g => ∀{p : α}, ∀h : p ∈ inst.prime, t ≤ p → satisfies (⟨p,h⟩*).val f ∨ satisfies (⟨p,h⟩*).val g
    | Form.impl f g => ∀{u : α}, satisfies u f → satisfies (t ∘ u) g
    --can't pattern match using ⊃ because of collision with set

infix:128 "⊨"  => satisfies

theorem satisfactionUp [inst : Model α] {s t : α} {f : Form} (h₁: s ≤ t) (h₂ : s ⊨ f) : t ⊨ f := 
  match f with
    | #n => have l₁ : inst.valuation s ⊆ inst.valuation t := inst.valMonotone s t h₁
            l₁ h₂
    | ~g => by unfold satisfies
               intros p h₃ h₄ h₅
               exact h₂ h₃ (le_trans' h₄ h₁) h₅
    | f & g => by unfold satisfies
                  apply And.intro
                  case left => exact satisfactionUp h₁ h₂.left
                  case right => exact satisfactionUp h₁ h₂.right
    | f ¦ g => by unfold satisfies
                  intros p h₃ h₄
                  apply Or.elim (h₂ h₃ (le_trans' h₄ h₁))
                  case left => intro h₅; exact Or.inl h₅
                  case right => intro h₅; exact Or.inr h₅
    | Form.impl f g => by unfold satisfies
                          intros u h₃
                          let l₁ : s ∘ u ≤ t ∘ u := inst.appMonotoneRight u h₁
                          let l₂ : (s ∘ u) ⊨ g := h₂ h₃
                          exact satisfactionUp l₁ l₂
