import Mathlib.Init.Set
import Mathlib.Init.Algebra.Order
import Mathlib.Order.Monotone.Basic
import Mathlib.Logic.Function.Basic

class Model (α : Type u) 
  extends 
    PartialOrder α 
  where
    prime : Set α
    application : α → α → α
    identity : α
    routeleyStar : Subtype prime → Subtype prime
    valuation : α → Set Nat
    appMonotoneLeft : ∀x : α, Monotone (application x)
    appMonotoneRight : ∀x : α, Monotone (flip application x)
    appBounding : ∀t u : α, ∀p : Subtype prime, application t u ≤ p → 
                      ∃q r : Subtype prime, t ≤ q ∧ u ≤ r ∧ application q u ≤ p ∧ application t r ≤ p
    appLeftIdent : ∀x : α, application identity x = x
    valMonotone : ∀x y : α, x ≤ y → valuation x ⊆ valuation y
    valBounding : ∀t : α, ∀x : Nat, (∀p : Subtype prime, t ≤ p → x ∈ valuation p) → x ∈ valuation t
    starAntitone : Antitone routeleyStar
    starInvolution: Function.Involutive routeleyStar

abbrev Model.primes [m : Model α] : Type := Subtype m.prime

infix:256 "∘" => Model.application --overloading composition symbol here
postfix:256 "*" => Model.routeleyStar
