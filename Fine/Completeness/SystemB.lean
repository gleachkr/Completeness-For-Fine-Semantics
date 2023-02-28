import Fine.Semantics.Model
import Fine.Semantics.Satisfaction
import Fine.Hilbert.SystemB
import Fine.PropositionalLanguage

def formalTheory (Γ : Ctx) : Prop := ∀f : Form, f ∈ Γ ↔ Γ ⊢ f

def generatedTheory (Γ : Ctx) : Ctx := BProvable Γ

prefix:512 "▲" => generatedTheory

theorem generatedFormal : ∀Γ : Ctx, formalTheory (▲Γ) := by
   unfold formalTheory
   intros Γ f
   apply Iff.intro
   case mp =>
      intros h₁
      exact ⟨BProof.ax h₁, trivial⟩
   case mpr =>
      intros h₁
      cases h₁; rename_i w _; induction w
      case intro.ax => assumption
      case intro.mp => 
        rename_i _ P Q _ h₂ ih
        have ⟨prf,_⟩ := ih
        exact ⟨BProof.mp prf h₂, trivial⟩
      case intro.adj => 
        rename_i ih₁ ih₂
        have ⟨prf₁,_⟩ := ih₁
        have ⟨prf₂,_⟩ := ih₂
        exact ⟨BProof.adj prf₁ prf₂, trivial⟩

def DisjunctionClosed (Γ : Ctx) := ∀f g : Form, f ∈ Γ ∧ g ∈ Γ → f ¦ g ∈ Γ

def PrimeTheory (Γ : Ctx) := ∀f g : Form, f ¦ g ∈ Γ → f ∈ Γ ∨ g ∈ Γ

def FormalApplication (Γ : Ctx) (Δ : Ctx) : Ctx := 
  λf : Form => ∃g : Form, g ∈ Δ ∧ (g ⊃ f) ∈ Γ

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
    case a.mp => 
      intros a
      exact (h₁ x).mpr a
    case a.mpr =>
      intros a
      exact (h₁ x).mp a

lemma BisFormal : formalTheory BTheory := by
  unfold formalTheory
  intros f
  apply Iff.intro
  case mp => intro a; exact ⟨BProof.ax a, trivial⟩
  case mpr =>
    intro h₁
    have ⟨prf₁,_⟩ := h₁
    induction prf₁
    case ax _ P ih => assumption
    case mp _ P Q prf₁ thm₁ ih => 
      have l₁ := ih ⟨prf₁,trivial⟩
      have ⟨thm₂,_⟩ := l₁
      exact ⟨BTheorem.mp thm₂ thm₁, trivial⟩
    case adj _ P Q prf₁ prf₂ ih₁ ih₂ =>
      have ⟨l₁,_⟩ := ih₁ ⟨prf₁,trivial⟩
      have ⟨l₂,_⟩ := ih₂ ⟨prf₂,trivial⟩
      exact ⟨BTheorem.adj l₁ l₂, trivial⟩
