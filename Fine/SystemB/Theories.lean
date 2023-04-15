import Fine.Semantics.Model
import Fine.Semantics.Satisfaction
import Fine.SystemB.Hilbert
import Fine.PropositionalLanguage

def formalTheory (Γ : Ctx) : Prop := ∀{f : Form}, f ∈ Γ ↔ Γ ⊢ f

abbrev Th := { Γ : Ctx // formalTheory Γ }

instance : Membership Form Th where
  mem f Γ := f ∈ Γ.val

def generatedTheory (Γ : Ctx) : Ctx := BProvable Γ

prefix:512 "▲" => generatedTheory

theorem generatedFormal : ∀Γ : Ctx, formalTheory (▲Γ) := by
   unfold formalTheory
   intros Γ f
   apply Iff.intro
   case mp => 
      intros h₁
      exact Nonempty.intro $ BProof.ax h₁
   case mpr =>
     intros h₁  
     have ⟨w⟩ := h₁
     induction w
     case ax => assumption
     case mp P Q prf thm ih => 
       have ⟨prf₂⟩ := ih ⟨prf⟩
       exact ⟨BProof.mp prf₂ thm⟩
     case adj P Q prf₁ prf₂ ih₁ ih₂ => 
       have ⟨prf₃⟩ := ih₁ ⟨prf₁⟩
       have ⟨prf₄⟩ := ih₂ ⟨prf₂⟩
       exact ⟨BProof.adj prf₃ prf₄⟩

def isDisjunctionClosed (Γ : Ctx) := ∀{f g : Form}, f ∈ Γ ∧ g ∈ Γ → f ¦ g ∈ Γ

def isPrimeTheory (Γ : Ctx) := ∀{f g : Form}, f ¦ g ∈ Γ → f ∈ Γ ∨ g ∈ Γ

abbrev Pr := { Γ : Th // isPrimeTheory Γ }

instance : Membership Form Pr where
  mem f Γ := f ∈ Γ.val

def FormalDual (Γ : Ctx) : Ctx := 
  λf : Form => ¬(~f ∈ Γ)

lemma generatedDisjunction {f g h: Form} : f ∈ ▲{g} ∧ f ∈ ▲{h} → f ∈ ▲{g ¦ h} := by
  intros h₁
  have ⟨⟨prf₁⟩,⟨prf₂⟩⟩ := h₁
  have l₁ := prf₁.toTheorem
  have l₂ := prf₂.toTheorem
  have l₃ := (BTheorem.mp (BTheorem.adj l₁ l₂) BTheorem.orE)
  exact ⟨l₃.toProof⟩

lemma generatedContained {Γ : Ctx } { Δ : Th } : Γ ⊆ Δ → ▲Γ ⊆ Δ := by
  intros h₁ f h₂
  have ⟨prf⟩ := h₂
  induction prf
  case ax p ih => exact h₁ ih
  case mp p q prf₁ prf₂ ih => 
    have l₁ := ih ⟨prf₁⟩
    have ⟨prf₃⟩ := Δ.property.mp l₁
    exact Δ.property.mpr ⟨BProof.mp prf₃ prf₂⟩
  case adj p q prf₁ prf₂ ih₁ ih₂ => 
    have l₁ := ih₁ ⟨prf₁⟩
    have l₂ := ih₂ ⟨prf₂⟩
    have ⟨prf₃⟩ := Δ.property.mp l₁
    have ⟨prf₄⟩ := Δ.property.mp l₂
    exact Δ.property.mpr ⟨BProof.adj prf₃ prf₄⟩

lemma formalFixed {Γ : Ctx} : formalTheory Γ → ▲Γ = Γ := by
  intros h₁
  funext
  case h x =>
    ext
    apply Iff.intro
    · intros a
      exact h₁.mpr a
    · intros a
      exact h₁.mp a

lemma BisFormal : formalTheory BTheory := by
  intros f
  apply Iff.intro
  · intro a
    exact ⟨BProof.ax a⟩
  · intro h₁
    have ⟨prf₁⟩ := h₁
    induction prf₁
    . assumption
    case mp P Q prf₁ thm₁ ih => 
      have l₁ := ih ⟨prf₁⟩
      have ⟨thm₂⟩ := l₁
      exact ⟨BTheorem.mp thm₂ thm₁⟩
    case adj P Q prf₁ prf₂ ih₁ ih₂ =>
      have ⟨l₁⟩ := ih₁ ⟨prf₁⟩
      have ⟨l₂⟩ := ih₂ ⟨prf₂⟩
      exact ⟨BTheorem.adj l₁ l₂⟩

abbrev BTh : Th := ⟨BTheory, BisFormal⟩

def formalApplication (Γ : Ctx) (Δ : Ctx) : Ctx := λf : Form => ∃g : Form, g ∈ Δ ∧ (g ⊃ f) ∈ Γ

theorem formalAppMonotoneLeft : ∀Γ : Ctx, Monotone (formalApplication Γ) := by
  intros Γ a b h₁ A h₂
  have ⟨g,h₃⟩ := h₂
  exact ⟨g, h₁ h₃.left, h₃.right⟩

theorem formalAppMonotoneRight : ∀Γ : Ctx, Monotone (flip formalApplication Γ) := by
  intros Γ a b h₁ A h₂
  have ⟨g,h₃⟩ := h₂
  exact ⟨g, h₃.left, h₁ h₃.right⟩



  
def formalApplicationFunction : Th → Th → Th
  | ⟨Δ, h₁⟩, ⟨Γ, h₂⟩ => by
    apply Subtype.mk
    case val => exact formalApplication Δ Γ
    case property =>
      intros f
      apply Iff.intro
      intros h₁
      case mp => exact ⟨BProof.ax h₁⟩
      case mpr =>
        intros h₂
        have ⟨prf⟩ := h₂
        induction prf
        case ax => assumption
        case mp _ P Q prf thm ih₁ =>
          have ⟨R, l₁⟩ := ih₁ ⟨prf⟩
          have prf₂ := BProof.ax l₁.2
          have l₃ := BProof.mp prf₂ (BTheorem.transitivityRight thm)
          have l₄ := h₁.mpr ⟨l₃⟩
          exact ⟨R, l₁.1, l₄⟩
        case adj h₃ P Q prf₁ prf₂ ih₁ ih₂ =>
          unfold formalApplication
          have ⟨R, l₁⟩ := ih₁ ⟨prf₁⟩
          have prf₃ := BProof.ax l₁.2
          have ⟨S, l₂⟩ := ih₂ ⟨prf₂⟩
          have prf₄ := BProof.ax l₂.2
          have l₃ : BProof Δ (R & S ⊃ P) := BProof.mp prf₃ (BTheorem.transitivityLeft BTheorem.andE₁) 
          have l₄ : BProof Δ (R & S ⊃ Q) := BProof.mp prf₄ (BTheorem.transitivityLeft BTheorem.andE₂) 
          have l₅ : BProof Δ (R & S ⊃ P & Q) := BProof.mp (BProof.adj l₃ l₄) BTheorem.andI
          have l₆ : BProof Γ (R & S) := BProof.adj (BProof.ax l₁.1) (BProof.ax l₂.1)
          exact ⟨R&S, h₃.mpr ⟨l₆⟩, h₁.mpr ⟨l₅⟩⟩

example {Γ : Th} {Δ : Th} : formalApplication Γ Δ = formalApplicationFunction Γ Δ := rfl

theorem formalAppFunctionMonotoneRight : ∀Γ : Th, Monotone (flip formalApplicationFunction Γ) := by
  intros Γ _ _ h₁
  exact formalAppMonotoneRight Γ h₁

theorem formalAppFunctionMonotoneLeft : ∀Γ : Th, Monotone (formalApplicationFunction Γ) := by
  intros Γ _ _ h₁
  exact formalAppMonotoneLeft Γ h₁

theorem formalAppIdentLeft : ∀Γ : Th, formalApplicationFunction BTh Γ = Γ := by
  intros Γ
  ext f
  apply Iff.intro
  case a.h.mp =>
    intros h₁
    have ⟨g,h₂,⟨h₃⟩⟩ := h₁
    exact Γ.property.mpr ⟨BProof.mp (BProof.ax h₂) h₃⟩
  case a.h.mpr =>
    intros h₁
    exact ⟨f, h₁, ⟨BTheorem.taut⟩⟩

theorem formalStarFormal (Γ : Ctx) (h₁: formalTheory Γ) (h₂ : isPrimeTheory Γ) : formalTheory (FormalDual Γ) := by
  intros F
  apply Iff.intro <;> intros h₃ <;> unfold FormalDual
  case mp => exact ⟨BProof.ax h₃⟩
  case mpr =>
    have ⟨prf₁⟩ := h₃
    induction prf₁
    case ax => assumption
    case mp P Q prf₂ thm₁ ih₁ =>
      intros h₄
      have l₁ := ih₁ ⟨prf₂⟩
      unfold FormalDual at l₁
      have thm₂ : BTheorem (~Q ⊃ ~P) := BTheorem.cp $ BTheorem.transitivity thm₁ (BTheorem.cp BTheorem.taut)
      have prf₂ := BProof.mp (BProof.ax h₄) thm₂
      exact l₁ (h₁.mpr ⟨prf₂⟩) 
    case adj P Q prf₁ prf₂ ih₁ ih₂ =>
      intros h₄
      have l₁ := ih₁ ⟨prf₁⟩
      have l₂ := ih₂ ⟨prf₂⟩
      have prf₃ := BProof.mp (BProof.ax h₄) BTheorem.demorgansLaw3
      have l₃ := h₂ (h₁.mpr ⟨prf₃⟩)
      cases l₃
      case inl left => exact l₁ left
      case inr right => exact l₂ right
  
section

open Classical

def primeStarFunction (Γ : Pr) : Pr := by
    unfold Pr
    apply Subtype.mk
    case val => exact ⟨FormalDual Γ, formalStarFormal Γ.1.1 Γ.1.2 Γ.2⟩
    case property => 
      unfold isPrimeTheory
      intros P Q h₃
      apply byContradiction
      intros h₄
      have l₁ : P¦Q ∈ FormalDual Γ := h₃
      have l₂ : ¬(P ∈ FormalDual Γ ∨ Q ∈ FormalDual Γ) := h₄
      have l₃ : ~P ∈ Γ.1.1 := byContradiction $ λh => l₂ $ Or.inl h
      have l₄ : ~Q ∈ Γ.1.1 := byContradiction $ λh => l₂ $ Or.inr h
      have l₅ : ~(P ¦ Q) ∈ Γ.1.1 := Γ.1.2.mpr $ ⟨BProof.mp (BProof.adj (BProof.ax l₃) (BProof.ax l₄)) BTheorem.demorgansLaw4⟩
      exact l₁ l₅

example {Γ : Pr} : FormalDual Γ = primeStarFunction Γ := rfl

theorem starInvolution : Function.Involutive primeStarFunction := by
  intros Γ
  ext f
  apply Iff.intro
  all_goals intros h₁
  case a.a.h.mpr =>
    intros h₂
    have l₁ : ~~f ∈ Γ := Γ.val.property.mpr ⟨BProof.mp (BProof.ax h₁) BTheorem.dni⟩
    exact h₂ l₁
  case a.a.h.mp =>
    apply byContradiction
    intros h₂
    have l₂ : ¬(~~f ∈ Γ) := h₂ ∘ λel => Γ.val.property.mpr ⟨BProof.mp (BProof.ax el) BTheorem.dne⟩
    exact h₁ l₂

theorem starAntitone : Antitone primeStarFunction := by
  intros _ _ h₁ f h₂ h₃
  exact h₂ (h₁ h₃)

end
