import Mathlib.Init.Set
import Mathlib.Logic.Denumerable
import Mathlib.Data.Finite.Defs

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

inductive ConsExp : Type
  | nat : Nat → ConsExp
  | cons : ConsExp → ConsExp → ConsExp

def ConsExp.encode : ConsExp → Nat
  | nat n => 2 * n
  | cons f g => 2 * Nat.mkpair f.encode g.encode + 1

def ConsExp.decode (n : ℕ) : ConsExp :=
  match hn : Nat.boddDiv2 n with
  | (false, m) => nat m
  | (true, m) =>
    match hm : Nat.unpair m with
    | (f, g) =>
      -- Some proofs to show termination:
      have hn' : 1 ≤ n := by
        cases n
        · simp at hn
        · simp [Nat.succ_eq_add_one]
      have : m < n := by
        have := congr_arg Prod.snd hn
        simp at this
        cases this
        apply Nat.binaryRec_decreasing
        rwa [Nat.one_le_iff_ne_zero] at hn'
      have : f < n := by
        apply Nat.lt_of_le_of_lt _ this
        have := congr_arg Prod.fst hm
        simp at this
        cases this
        cases m
        · simp
        next m =>
          apply (Nat.unpair_lt _).le
          simp [Nat.succ_eq_add_one]
      have : g < n := by
        have := congr_arg Prod.snd hm
        simp at this
        cases this
        have := Nat.unpair_right_le m
        apply Nat.lt_of_le_of_lt this
        assumption
      -- With those out of the way:
      cons (decode f) (decode g)
termination_by _ => n

theorem ConsExp.decode_encode (c : ConsExp) : ConsExp.decode c.encode = c := by
  induction c
  · rw [encode, decode]
    split
    next h =>
      simp [Nat.div2_val] at h
      simp [*]
    next h => simp at h
  next hf hg =>
    rw [encode, decode]
    split
    next h => simp at h
    next h =>
      simp [Nat.div2_val] at h
      cases h
      simp [*]

instance : Encodable ConsExp where
  encode := ConsExp.encode
  decode := fun v => some (ConsExp.decode v)
  encodek := fun a => by simp [ConsExp.decode_encode]

def Form.toConsExp : Form → ConsExp
  | atom n => .cons (.nat 0) (.nat n)
  | neg f => .cons (.nat 1) f.toConsExp
  | and f g => .cons (.nat 2) (.cons f.toConsExp g.toConsExp)
  | or f g => .cons (.nat 3) (.cons f.toConsExp g.toConsExp)
  | impl f g => .cons (.nat 4) (.cons f.toConsExp g.toConsExp)

theorem Form.toConsExp_injective : Function.Injective Form.toConsExp := by
  intros f1 f2
  induction f1 generalizing f2 <;> cases f2 <;> simp! <;> aesop

def ConsExp.toForm : ConsExp → Option Form
  | .cons (.nat 0) (.nat n) => .some (.atom n)
  | .cons (.nat 1) f => .neg <$> f.toForm
  | .cons (.nat 2) (.cons f g) => .and <$> f.toForm <*> g.toForm
  | .cons (.nat 3) (.cons f g) => .or <$> f.toForm <*> g.toForm
  | .cons (.nat 4) (.cons f g) => .impl <$> f.toForm <*> g.toForm
  | _ => .none

theorem toForm_toConsExp_eq (f : Form) : f.toConsExp.toForm = some f := by
  induction f <;> simp! [*]

instance : Encodable Form where
  encode f := Encodable.encode f.toConsExp
  decode n := Option.bind (Encodable.decode n) ConsExp.toForm 
  encodek := by
    intro f
    simp [toForm_toConsExp_eq]
    
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
