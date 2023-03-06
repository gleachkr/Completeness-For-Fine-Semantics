import Mathlib.Logic.Denumerable

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
