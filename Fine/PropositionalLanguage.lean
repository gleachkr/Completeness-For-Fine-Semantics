import Mathlib.Init.Set
import Mathlib.Logic.Denumerable
import Fine.Util.ConsExp

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

def Form.toConsExp : Form → ConsExp
  | atom n => .cons (.nat 0) (.nat n)
  | neg f => .cons (.nat 1) f.toConsExp
  | and f g => .cons (.nat 2) (.cons f.toConsExp g.toConsExp)
  | or f g => .cons (.nat 3) (.cons f.toConsExp g.toConsExp)
  | impl f g => .cons (.nat 4) (.cons f.toConsExp g.toConsExp)

theorem Form.toConsExp_injective : Function.Injective Form.toConsExp := by
  intros f1 f2
  induction f1 generalizing f2 <;> cases f2 <;> simp! <;> aesop

theorem Form.nat_injection : Function.Injective Form.atom := by
  unfold Function.Injective;
  intros n m h₁
  injection h₁

def ConsExp.toForm : ConsExp → Option Form
  | .cons (.nat 0) (.nat n) => .some (.atom n)
  | .cons (.nat 1) f => .neg <$> f.toForm
  | .cons (.nat 2) (.cons f g) => .and <$> f.toForm <*> g.toForm
  | .cons (.nat 3) (.cons f g) => .or <$> f.toForm <*> g.toForm
  | .cons (.nat 4) (.cons f g) => .impl <$> f.toForm <*> g.toForm
  | _ => .none

instance {f : Form} : Decidable (∃g h, f = g ¦ h) := by
  cases f
  case or f₁ f₂ => exact isTrue ⟨f₁, f₂, rfl⟩
  repeat
    apply isFalse
    intros h₁
    have ⟨g, h, h₂⟩ := h₁
    injection h₂

theorem toForm_toConsExp_eq (f : Form) : f.toConsExp.toForm = some f := by
  induction f <;> simp! [*]

instance Form.infinite : Infinite Form := 
  Infinite.of_injective Form.atom Form.nat_injection

def Form.encodable : Encodable Form where
  encode f := Encodable.encode f.toConsExp
  decode n := Option.bind (Encodable.decode n) ConsExp.toForm 
  encodek := by
    intro f
    simp [toForm_toConsExp_eq]

instance : Denumerable Form := @Denumerable.ofEncodableOfInfinite Form Form.encodable Form.infinite

instance Form.disjunctions_encodable : Encodable {f : Form // ∃g h : Form, f = g ¦ h} := Encodable.Subtype.encodable

instance Form.disjunctions_infinite : Infinite {f : Form // ∃g h : Form, f = g ¦ h} := by
  apply Infinite.of_injective (λn : Nat => ⟨#n ¦ #n, ⟨#n, #n, rfl⟩⟩)
  unfold Function.Injective
  intros n₁ n₂ h₁
  injection h₁ with h₁
  injection h₁ with h₁ h₂
  injection h₁

instance : Denumerable {f : Form // ∃g h : Form, f = g ¦ h} := 
  Denumerable.ofEncodableOfInfinite {f : Form // ∃g h : Form, f = g ¦ h}
    
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

def Form.conjoinList (f : Form) : List Form → Form
  | [] => f
  | a :: as => a & Form.conjoinList f as
