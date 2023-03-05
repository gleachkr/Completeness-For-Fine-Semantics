import Mathlib.Init.Set
import Mathlib.Logic.Denumerable

inductive Form : Type
  | atom : Nat → Form
  | neg  : Form → Form
  | and  : Form → Form → Form
  | or   : Form → Form → Form
  | impl : Form → Form → Form
  deriving DecidableEq

prefix:max "#" => Form.atom
infix:256 "⊃"  => Form.impl
infixr:512 "&" => Form.and
infixr:512 "¦" => Form.or
prefix:max "~" => Form.neg

abbrev tupleEquiv := Nat⊕ Nat⊕ (Nat × Nat)⊕ (Nat × Nat)⊕ (Nat×Nat)

def toSumEncoding : Form → Nat⊕ Nat⊕ (Nat × Nat)⊕ (Nat × Nat)⊕ (Nat×Nat)
    | #n => Sum.inl n
    | ~f => Sum.inr $ Sum.inl (Encodable.encode $ toSumEncoding f)
    | f & g => Sum.inr $ Sum.inr $ Sum.inl ⟨Encodable.encode $ toSumEncoding f, Encodable.encode $ toSumEncoding g⟩
    | f ¦ g => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl ⟨Encodable.encode $ toSumEncoding f, Encodable.encode $ toSumEncoding g⟩
    | Form.impl f g => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr ⟨Encodable.encode $ toSumEncoding f, Encodable.encode $ toSumEncoding g⟩

theorem sum_encoding_injection : Function.Injective toSumEncoding := by
  unfold Function.Injective
  intros P
  induction P
  case atom n =>
    intros Q h₁
    cases Q
    · unfold toSumEncoding at h₁
      injection h₁ with h₁
      rw [h₁]
    repeat (unfold toSumEncoding at h₁; injection h₁)
  case neg Q ih =>
    intros R h
    cases R
    case neg S =>
      unfold toSumEncoding at h
      repeat (injection h with h)
      have l := ih (Encodable.encode_injective h)
      simp [l]
    repeat
      unfold toSumEncoding at h
      repeat (injection h with h)
      injection h
  case and =>
    rename_i R S ih₁ ih₂
    intros T h₁
    cases T
    case and U V =>
      unfold toSumEncoding at h₁
      repeat (injection h₁ with h₁)
      rename_i h₂
      have l₁ := ih₁ (Encodable.encode_injective h₁)
      have l₂ := ih₂ (Encodable.encode_injective h₂)
      simp [l₁,l₂]
    repeat
      unfold toSumEncoding at h₁
      repeat (injection h₁ with h₁)
      injection h₁
  case or =>
    rename_i R S ih₁ ih₂
    intros T h₁
    cases T
    case or U V =>
      unfold toSumEncoding at h₁
      repeat (injection h₁ with h₁)
      rename_i h₂
      have l₁ := ih₁ (Encodable.encode_injective h₁)
      have l₂ := ih₂ (Encodable.encode_injective h₂)
      simp [l₁,l₂]
    repeat
      unfold toSumEncoding at h₁
      repeat (injection h₁ with h₁)
      injection h₁
  case impl => 
    rename_i R S ih₁ ih₂
    intros T h₁
    cases T
    case impl U V =>
      unfold toSumEncoding at h₁
      repeat (injection h₁ with h₁)
      rename_i h₂
      have l₁ := ih₁ (Encodable.encode_injective h₁)
      have l₂ := ih₂ (Encodable.encode_injective h₂)
      simp [l₁,l₂]
    repeat
      unfold toSumEncoding at h₁
      repeat (injection h₁ with h₁)
      injection h₁
    
instance : ToString Form where
  toString := display
  where display: Form → String
    | #n => s!"A{n}"
    | ~f => "~" ++ display f
    | f1 & f2 => "(" ++ display f1 ++ "&" ++ display f2 ++ ")"
    | f1 ¦ f2 => "(" ++ display f1 ++ "¦" ++ display f2 ++ ")"
    | Form.impl f1 f2 => "(" ++ display f1 ++ " ⊃ " ++ display f2 ++ ")" 
    --can't pattern match using ⊃ because of collision with set


#check (#1 ⊃ ~(~#2 ⊃ #3) : Form )
#eval (#1 ⊃ ~(~#2 ⊃ #3) : Form )

abbrev Ctx := Set Form

instance instMembership : Membership Form Ctx where
  mem p Γ := Γ p
