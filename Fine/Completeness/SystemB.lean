import Fine.Semantics.Model
import Fine.Semantics.Satisfaction
import Fine.Hilbert.SystemB
import Fine.PropositionalLanguage
import Mathlib.Data.Finset.Basic
import Mathlib.Init.Set

def formalTheory (Γ : Ctx) : Prop := ∀{f : Form}, f ∈ Γ ↔ Γ ⊢ f

abbrev Th := { Γ : Ctx // formalTheory Γ }

def generatedTheory (Γ : Ctx) : Ctx := BProvable Γ

prefix:512 "▲" => generatedTheory

theorem generatedFormal : ∀Γ : Ctx, formalTheory (▲Γ) := by
   unfold formalTheory
   intros Γ f
   apply Iff.intro
   · intros h₁
     exact ⟨BProof.ax h₁, trivial⟩
   · intros h₁; cases h₁; rename_i w _; induction w
     case intro.ax => assumption
     case intro.mp _ _ _ _ h₂ ih => 
       have ⟨prf,_⟩ := ih
       exact ⟨BProof.mp prf h₂, trivial⟩
     case intro.adj ih₁ ih₂ => 
       have ⟨prf₁,_⟩ := ih₁
       have ⟨prf₂,_⟩ := ih₂
       exact ⟨BProof.adj prf₁ prf₂, trivial⟩

def DisjunctionClosed (Γ : Ctx) := ∀{f g : Form}, f ∈ Γ ∧ g ∈ Γ → f ¦ g ∈ Γ

def PrimeTheory (Γ : Ctx) := ∀{f g : Form}, f ¦ g ∈ Γ → f ∈ Γ ∨ g ∈ Γ

abbrev Pr := { Γ : Th // PrimeTheory Γ }

def FormalDual (Γ : Ctx) : Ctx := 
  λf : Form => ¬(~f ∈ Γ)

lemma generatedDisjunction {f g h: Form} : f ∈ ▲{g} ∧ f ∈ ▲{h} → f ∈ ▲{g ¦ h} := by
  intros h₁
  have ⟨⟨prf₁,_⟩,prf₂,_⟩ := h₁
  have l₁ := BTheorem.fromProof prf₁
  have l₂ := BTheorem.fromProof prf₂
  have l₃ := (BTheorem.mp (BTheorem.adj l₁ l₂) BTheorem.orE)
  exact ⟨BTheorem.toProof l₃, trivial⟩

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
  unfold formalTheory
  intros f
  apply Iff.intro
  · intro a
    exact ⟨BProof.ax a, trivial⟩
  · intro h₁
    have ⟨prf₁,_⟩ := h₁
    induction prf₁
    . assumption
    case mp _ P Q prf₁ thm₁ ih => 
      have l₁ := ih ⟨prf₁,trivial⟩
      have ⟨thm₂,_⟩ := l₁
      exact ⟨BTheorem.mp thm₂ thm₁, trivial⟩
    case adj _ P Q prf₁ prf₂ ih₁ ih₂ =>
      have ⟨l₁,_⟩ := ih₁ ⟨prf₁,trivial⟩
      have ⟨l₂,_⟩ := ih₂ ⟨prf₂,trivial⟩
      exact ⟨BTheorem.adj l₁ l₂, trivial⟩

theorem BProof.compactness { Γ : Ctx } { f : Form } : BProof Γ f → Σs : Finset Form, BProof ↑s f := by
  intros prf₁; induction prf₁
  case ax g _ => 
    have l₁ : g ∈ {g} := Finset.mem_singleton.mpr rfl
    have l₂ : ({g} : Finset Form) = ({g} : Ctx) := Finset.coe_singleton g
    have prf₂ : BProof ↑{g} g := by
      rw [←l₂]
      apply ax l₁
    rw [←l₂] at prf₂
    exact ⟨↑{g}, prf₂⟩
  case mp P Q _ h₂ ih => 
    have ⟨fin, prf⟩ := ih
    exact ⟨fin, mp prf h₂⟩
  case adj P Q _ _ ih₁ ih₂ => 
    have ⟨fin₁, prf₁⟩ := ih₁
    have ⟨fin₂, prf₂⟩ := ih₂
    have prf₃ : BProof (↑fin₁ ∪ ↑fin₂) P := BProof.monotone (Set.subset_union_left ↑fin₁ ↑fin₂) prf₁
    have prf₄ : BProof (↑fin₁ ∪ ↑fin₂) Q := BProof.monotone (Set.subset_union_right ↑fin₁ ↑fin₂) prf₂
    have prf₅ := adj prf₃ prf₄
    rw [←Finset.coe_union] at prf₅
    exact ⟨↑(fin₁ ∪ fin₂), prf₅⟩

def FormalApplication (Γ : Ctx) (Δ : Ctx) : Ctx := λf : Form => ∃g : Form, g ∈ Δ ∧ (g ⊃ f) ∈ Γ
  
def formalApplicationFunction : Th → Th → Th
  | ⟨Δ, h₁⟩, ⟨Γ, h₂⟩ => by
    unfold Th; unfold formalTheory
    apply Subtype.mk
    case val => exact FormalApplication Δ Γ
    case property =>
      intros f
      apply Iff.intro
      intros h₁
      case mp => exact ⟨BProof.ax h₁, trivial⟩
      case mpr =>
        intros h₂
        have ⟨prf,_⟩ := h₂
        induction prf
        case ax => assumption
        case mp _ _ P Q prf thm ih₁ =>
          have ⟨R, l₁⟩ := ih₁ ⟨prf,trivial⟩
          have prf₂ := BProof.ax l₁.2
          have l₃ := BProof.mp prf₂ (BTheorem.transitivityRight thm)
          have l₄ := h₁.mpr ⟨l₃,trivial⟩
          exact ⟨R, l₁.1, l₄⟩
        case adj h₃ _ P Q prf₁ prf₂ ih₁ ih₂ =>
          unfold FormalApplication
          have ⟨R, l₁⟩ := ih₁ ⟨prf₁,trivial⟩
          have prf₃ := BProof.ax l₁.2
          have ⟨S, l₂⟩ := ih₂ ⟨prf₂,trivial⟩
          have prf₄ := BProof.ax l₂.2
          have l₃ : BProof Δ (R & S ⊃ P) := BProof.mp prf₃ (BTheorem.transitivityLeft BTheorem.andE₁) 
          have l₄ : BProof Δ (R & S ⊃ Q) := BProof.mp prf₄ (BTheorem.transitivityLeft BTheorem.andE₂) 
          have l₅ : BProof Δ (R & S ⊃ P & Q) := BProof.mp (BProof.adj l₃ l₄) BTheorem.andI
          have l₆ : BProof Γ (R & S) := BProof.adj (BProof.ax l₁.1) (BProof.ax l₂.1)
          exact ⟨R&S, h₃.mpr ⟨l₆, trivial⟩, h₁.mpr ⟨l₅,trivial⟩⟩

example {Γ : Th} {Δ : Th} : FormalApplication Γ Δ = formalApplicationFunction Γ Δ := rfl

theorem formalStarFormal (Γ : Ctx) (h₁: formalTheory Γ) (h₂ : PrimeTheory Γ) : formalTheory (FormalDual Γ) := by
  unfold formalTheory
  intros F
  apply Iff.intro <;> intros h₃ <;> unfold FormalDual
  case mp => exact ⟨BProof.ax h₃,trivial⟩
  case mpr =>
    have ⟨prf₁,_⟩ := h₃
    induction prf₁
    case ax => assumption
    case mp _ P Q prf₂ thm₁ ih₁ =>
      intros h₄
      have l₁ := ih₁ ⟨prf₂,trivial⟩
      unfold FormalDual at l₁
      have thm₂ : BTheorem (~Q ⊃ ~P) := BTheorem.cp $ BTheorem.transitivity thm₁ (BTheorem.cp BTheorem.taut)
      have prf₂ := BProof.mp (BProof.ax h₄) thm₂
      exact l₁ (h₁.mpr ⟨prf₂, trivial⟩) 
    case adj _ P Q prf₁ prf₂ ih₁ ih₂ =>
      intros h₄
      have l₁ := ih₁ ⟨prf₁,trivial⟩
      have l₂ := ih₂ ⟨prf₂,trivial⟩
      have prf₃ := BProof.mp (BProof.ax h₄) BTheorem.demorgansLaw3
      have l₃ := h₂ (h₁.mpr ⟨prf₃, trivial⟩)
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
      unfold PrimeTheory
      intros P Q h₃
      apply byContradiction
      intros h₄
      have l₁ : P¦Q ∈ FormalDual Γ := h₃
      have l₂ : ¬(P ∈ FormalDual Γ ∨ Q ∈ FormalDual Γ) := h₄
      have l₃ : ~P ∈ Γ.1.1 := byContradiction $ λh => l₂ $ Or.inl h
      have l₄ : ~Q ∈ Γ.1.1 := byContradiction $ λh => l₂ $ Or.inr h
      have l₅ : ~(P ¦ Q) ∈ Γ.1.1 := Γ.1.2.mpr $ ⟨BProof.mp (BProof.adj (BProof.ax l₃) (BProof.ax l₄)) BTheorem.demorgansLaw4, trivial⟩
      exact l₁ l₅

example {Γ : Pr} : FormalDual Γ = primeStarFunction Γ := rfl

end
