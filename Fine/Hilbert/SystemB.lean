import Fine.PropositionalLanguage

inductive BTheorem : Form → Type
  | taut {p} : BTheorem (p ⊃ p)
  | andE₁ {p q} : BTheorem (p & q ⊃ p)
  | andE₂ {p q} : BTheorem (p & q ⊃ q)
  | andI {p q r} : BTheorem ((p ⊃ q) & (p ⊃ r) ⊃ (p ⊃ q & r))
  | orI₁ {p q} : BTheorem (p ⊃ p ¦ q)
  | orI₂ {p q} : BTheorem (q ⊃ p ¦ q)
  | orE {p q r} : BTheorem ((p ⊃ r) & (q ⊃ r) ⊃ (p ¦ q ⊃ r))
  | dne {p} : BTheorem (~~p ⊃ p)
  | dist {p q r} : BTheorem (p & (q ¦ r) ⊃ (p & q) ¦ (p & r))
  | mp {p q} (h₁ : BTheorem p) (h₂ : BTheorem (p ⊃ q)) : BTheorem q
  | adj {p q} (h₁ : BTheorem p) (h₂ : BTheorem q) : BTheorem (p & q)
  | cp {p q} (h₁ : BTheorem (p ⊃ ~q)) : BTheorem (q ⊃ ~p)
  | hs {p q r s} (h₁ : BTheorem (p ⊃ q)) (h₂ : BTheorem (r ⊃ s)) : BTheorem ((q ⊃ r) ⊃ (p ⊃ s))

inductive BProof : Ctx → Form → Type
  | ax {Γ} {p} (h: p ∈ Γ) : BProof Γ p
  | mp {Γ} {p} {q} (h₁ : BProof Γ p) (h₂ : BTheorem (p ⊃ q)) : BProof Γ q
  | adj {Γ} {p} {q} (h₁ : BProof Γ p) (h₂ : BProof Γ q) : BProof Γ (p & q)

abbrev BProvable (Γ : Ctx) (f : Form) : Prop:= Nonempty (BProof Γ f)

abbrev BTheory (f : Form) : Prop := Nonempty (BTheorem f)

infix:128 "⊢" => BProvable

section

open BTheorem

variable {p q r s : Form} 

def BTheorem.transitivity (h₁ : BTheorem (p ⊃ q)) (h₂ : BTheorem (q ⊃ r)) : BTheorem (p ⊃ r) :=
  mp taut (hs h₁ h₂) 

def BTheorem.transitivityLeft (h : BTheorem (p ⊃ q)) : BTheorem ((q ⊃ r) ⊃ (p ⊃ r)) :=
  hs h taut
  
def BTheorem.transitivityRight (h : BTheorem (p ⊃ q)) : BTheorem ((r ⊃ p) ⊃ (r ⊃ q)) :=
  hs taut h

def BTheorem.commAnd : BTheorem (q & p ⊃ p & q) :=
  BTheorem.mp (BTheorem.adj BTheorem.andE₂ BTheorem.andE₁) BTheorem.andI

def BTheorem.distRight : BTheorem ((q ¦ r) & p ⊃ (q & p) ¦ (r & p)) :=
  have l₁ : BTheorem ((q ¦ r) & p ⊃ (p & q) ¦ (p & r)) := BTheorem.transitivity BTheorem.commAnd BTheorem.dist
  have l₂ : BTheorem ((p & q) ¦ (p & r) ⊃ (q & p) ¦ (r & p)) := BTheorem.mp 
     (BTheorem.adj (BTheorem.transitivity BTheorem.commAnd BTheorem.orI₁) (BTheorem.transitivity BTheorem.commAnd BTheorem.orI₂))
     BTheorem.orE
  BTheorem.transitivity l₁ l₂

def BTheorem.demorgansLaw1 : BTheorem ((p & q) ⊃ ~(~p ¦ ~q)) := 
  have l₁ : ∀{r : Form}, BTheorem (r ⊃ ~~r) := cp taut
  have l₂ : BTheorem (~p ⊃ ~(p & q)) := cp $ mp taut (hs andE₁ l₁)
  have l₃ : BTheorem (~q ⊃ ~(p & q)) := cp $ mp taut (hs andE₂ l₁)
  cp $ mp (adj l₂ l₃) orE

def BTheorem.demorgansLaw2 : BTheorem (~(~p ¦ ~q) ⊃ (p & q)) := 
  have l₁ : BTheorem (~p ⊃ ~~(~p ¦ ~q)) := transitivity orI₁ (cp taut)
  have l₂ : BTheorem (~(~p ¦ ~q) ⊃ p ) := transitivity (cp l₁) dne
  have l₃ : BTheorem (~q ⊃ ~~(~p ¦ ~q)) := transitivity orI₂ (cp taut)
  have l₄ : BTheorem (~(~p ¦ ~q) ⊃ q ) := transitivity (cp l₃) dne
  mp (adj l₂ l₄) andI

def BTheorem.demorgansLaw3 : BTheorem (~(p & q) ⊃ (~p ¦ ~q)) := 
  have l₁ : BTheorem (~(~p ¦ ~q) ⊃ ~~(p & q)):= transitivity demorgansLaw2 (cp taut)
  transitivity (cp l₁) dne

def BTheorem.demorgansLaw4 : BTheorem ((~p & ~q) ⊃ ~(p ¦ q)) := 
  have l₁ : BTheorem (p ⊃ ~(~p & ~q)) := cp andE₁
  have l₂ : BTheorem (q ⊃ ~(~p & ~q)) := cp andE₂
  cp (mp (adj l₁ l₂) orE)

def BTheorem.fromProof { p q : Form } : BProof {p} q → BTheorem (p ⊃ q)
  | BProof.ax h => by rw [h]; exact taut
  | BProof.adj h₁ h₂ => mp (adj (fromProof h₁) (fromProof h₂)) andI
  | BProof.mp h₁ h₂ => transitivity (fromProof h₁) h₂

def BTheorem.toProof { p q : Form } (h₁ : BTheorem (p ⊃ q)) : BProof {p} q := 
  BProof.mp (BProof.ax rfl) h₁

example : BTheorem ((p ⊃ q) ⊃ (p ⊃ (q ¦ r))) :=
  hs taut orI₁

example : BTheorem ((p ⊃ q) ⊃ (p & r ⊃ q)) :=
  hs andE₁ taut

def BProof.monotone { f : Form } { Γ : Ctx } { Δ : Ctx } (mono: Γ ⊆ Δ ) : BProof Γ f → BProof Δ f
  | ax h₁ => ax (mono h₁)
  | mp prf₁ thm₂ => mp (monotone mono prf₁) thm₂
  | adj prf₁ prf₂ => adj (monotone mono prf₁) (monotone mono prf₂)

def BProof.adjoinPremises { p q r : Form } : BProof {p,q} r → BProof {p & q} r
  | ax h => if c₁ : r = p then by
              rw [c₁]
              exact mp (ax rfl : BProof {p&q} (p&q)) andE₁
            else if c₂ : r = q then by
              rw [c₂]
              exact mp (ax rfl : BProof {p&q} (p&q)) andE₂
            else False.elim (Or.elim h c₁ c₂)
  | mp h₁ h₂ => mp (adjoinPremises h₁) h₂
  | adj h₁ h₂ => adj (adjoinPremises h₁) (adjoinPremises h₂)

def BProof.proveList { l : List Form } { f : Form } { Γ : Ctx } : { g | g ∈ f :: l } ⊆ Γ → BProof Γ (Form.conjoinList f l) := by
  intros h₁
  induction l
  case nil => 
    exact BProof.ax (h₁ $ List.mem_singleton.mpr rfl)
  case cons head tail ih =>
    have l₂ : { g | g ∈ f :: tail } ⊆ Γ := by
      intros g h₂
      cases h₂
      case head => exact h₁ $ List.mem_cons.mpr $ Or.inl rfl
      case tail h₃ => exact h₁ $ List.mem_cons.mpr $ Or.inr $ List.mem_cons.mpr $ Or.inr h₃
    have prf₁ := ih l₂
    have prf₂ := BProof.ax $ h₁ $ List.mem_cons.mpr $ Or.inr $ List.mem_cons.mpr $ Or.inl rfl
    cases tail
    case nil => exact BProof.adj prf₁ prf₂
    case cons head' tail' => 
      have prf₃ := BProof.mp prf₁ BTheorem.andE₁
      have prf₄ := BProof.mp prf₁ BTheorem.andE₂
      exact BProof.adj prf₃ $ BProof.adj prf₂ prf₄

def BProof.proveFromList { l : List Form } { f : Form } : g ∈ f :: l → BProof {Form.conjoinList f l} g := by
  intros h₁
  induction l
  case nil =>
    have l₁ : g = f := by
      cases List.mem_cons.mp h₁
      . assumption
      . contradiction
    rw [l₁]
    have l₂ : f ∈ ({f} : Ctx) := rfl
    exact BProof.ax l₂
  case cons head tail ih =>
      cases decEq g head
      case isFalse h₂ =>
        have l₁ : g ∈ f :: tail := by
          cases List.mem_cons.mp h₁
          case inl h₃ => exact List.mem_cons.mpr $ Or.inl h₃
          case inr h₃ => 
            cases List.mem_cons.mp h₃
            case inl => contradiction
            case inr h₄ => exact List.mem_cons.mpr $ Or.inr h₄
        have prf₁ := ih l₁
        cases tail
        case nil => 
          have prf₂ : BProof {Form.conjoinList f [head]} f := BProof.mp (BProof.ax rfl) BTheorem.andE₁
          exact BProof.mp prf₂ (BTheorem.fromProof prf₁)
        case cons head' tail' =>
          have prf₂ : BProof {Form.conjoinList f (head :: head' :: tail')} (Form.conjoinList f (head' :: tail')) := by
            exact BProof.adj (BProof.mp (BProof.ax rfl) BTheorem.andE₁) (BProof.mp (BProof.mp (BProof.ax rfl) BTheorem.andE₂) BTheorem.andE₂)
          exact BProof.mp prf₂ (BTheorem.fromProof prf₁)
      case isTrue h₂ =>
        rw [h₂]
        cases tail
        case nil => exact BProof.mp (BProof.ax rfl) BTheorem.andE₂
        case cons head' tail' => exact BProof.mp (BProof.mp (BProof.ax rfl) BTheorem.andE₂) BTheorem.andE₁

theorem BProof.compactness { Γ : Ctx } { f : Form } : BProof Γ f → Σs : Finset Form, Σ'_ : ↑s ⊆ Γ,  BProof ↑s f := by
  intros prf₁; induction prf₁
  case ax g h₁ => 
    let Gsing : Finset Form := {g} 
    have l₁ : g ∈ {g} := Finset.mem_singleton.mpr rfl
    have l₂ : Gsing = ({g} : Ctx) := Finset.coe_singleton g
    have l₃ : ↑Gsing ⊆ Γ := by
      intros g' h₂
      rw [l₂] at h₂
      rw [h₂]
      assumption
    have prf₂ : BProof ↑{g} g := by
      rw [←l₂]
      apply ax l₁
    rw [←l₂] at prf₂
    exact ⟨Gsing, l₃, prf₂⟩
  case mp P Q _ h₂ ih => 
    have ⟨fin, h₁, prf⟩ := ih
    exact ⟨fin, h₁, mp prf h₂⟩
  case adj P Q _ _ ih₁ ih₂ => 
    have ⟨fin₁, h₁, prf₁⟩ := ih₁
    have ⟨fin₂, h₂, prf₂⟩ := ih₂
    have prf₃ : BProof (↑fin₁ ∪ ↑fin₂) P := BProof.monotone (Set.subset_union_left ↑fin₁ ↑fin₂) prf₁
    have prf₄ : BProof (↑fin₁ ∪ ↑fin₂) Q := BProof.monotone (Set.subset_union_right ↑fin₁ ↑fin₂) prf₂
    have prf₅ := adj prf₃ prf₄
    have l₁ : ↑(fin₁ ∪ fin₂) ⊆ Γ := by
      intros f h₃
      rw [Finset.coe_union] at h₃
      cases h₃
      case inl h₄ => exact h₁ h₄
      case inr h₄ => exact h₂ h₄
    rw [←Finset.coe_union] at prf₅
    exact ⟨↑(fin₁ ∪ fin₂), l₁, prf₅⟩

theorem BProof.listCompression { l : List Form } { f : Form } {g : Form} : BProof {h : Form | h = f ∨ h ∈ l } g → BProof {Form.conjoinList f l} g  := by
  intros prf₁; induction prf₁
  case ax p h₁ => exact BProof.proveFromList $ List.mem_cons.mpr h₁
  case mp p q _ prf₂ ih => exact BProof.mp ih prf₂
  case adj p q _ _ prf₁ prf₂  => exact BProof.adj prf₁ prf₂

theorem BProof.sentenceCompactness { Γ : Ctx } { f g : Form } : BProof (insert f Γ) g → Σl : List Form, Σ'_ : {x | x ∈ l} ⊆ Γ,  BProof {Form.conjoinList f l} g := by
  intros h₁
  have ⟨s₁,h₂,prf₁⟩ := BProof.compactness h₁
  let lst₁ := (Finset.erase s₁ f).toList
  have l₁ : ↑s₁ ⊆ {h : Form | h = f ∨ h ∈ lst₁} := by
    intros k h₂
    cases decEq f k
    case isTrue h₃ => rw [h₃]; exact Or.inl rfl
    case isFalse h₃ => 
      have l₂ : k ∈ lst₁ := by
        apply Finset.mem_toList.mpr
        exact Finset.mem_erase.mpr ⟨h₃ ∘ Eq.symm, h₂⟩
      exact Or.inr l₂
  have prf₂ := BProof.listCompression $  BProof.monotone l₁ prf₁
  refine ⟨lst₁,?_,prf₂⟩
  intros k h₃
  have : k ∈ Finset.erase s₁ f := Finset.mem_toList.mp h₃
  have ⟨l₅,l₆⟩: k ≠ f ∧ k ∈ s₁ := Finset.mem_erase.mp this
  have : k ∈ insert f Γ := h₂ $ Finset.mem_coe.mpr l₆
  exact Set.mem_of_mem_insert_of_ne this l₅ 
    
end
