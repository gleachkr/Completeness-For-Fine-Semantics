import Fine.FormalTheories

open Classical

noncomputable def lindenbaumExtension (t : Th) (Δ : Ctx) : Nat → Nat → Ctx
  | 0, 0 => t.val
  | i + 1, 0 => { f : Form | ∃j : Nat, f ∈ lindenbaumExtension t Δ i j }
  | i, j + 1 => 
    have prev := lindenbaumExtension t Δ i j
    have ⟨l,r⟩ := Denumerable.ofNat (Form × Form) j
    if l ¦ r ∈ ▲prev 
    then if ▲(prev ∪ {l}) ∩ Δ = ∅
      then prev ∪ {l}
      else prev ∪ {r}
    else prev
  termination_by lindenbaumExtension t Δ i j => (i,j)
