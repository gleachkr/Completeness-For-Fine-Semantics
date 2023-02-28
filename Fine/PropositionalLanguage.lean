import Mathlib.Init.Set

inductive Form : Type
  | atom : Nat → Form
  | impl : Form → Form → Form
  | and  : Form → Form → Form
  | or   : Form → Form → Form
  | neg  : Form → Form
  deriving DecidableEq

prefix:max "#" => Form.atom
infix:256 "⊃"  => Form.impl
infixr:512 "&" => Form.and
infixr:512 "¦" => Form.or
prefix:max "~" => Form.neg

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
