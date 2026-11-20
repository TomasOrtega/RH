import Mathlib
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hb : β ∈ A` using `(A.valuation_le_one_iff β).mp hβ`. Establish `hb' : β' ∈ A` using `(A.valuation_le_one_iff β').mp hβ'`. Use `set b : A := ⟨β, hb⟩`. Use `set b' : A := ⟨β', hb'⟩`.

Take `⟨k, hk⟩` from `Polynomial.binomExpansion (f.map (algebraMap ℤ A)) b (b' - b)`. Rewrite `hk` using `[add_sub_cancel, derivative_map, eval_map_algebraMap, eval_map_algebraMap, eval_map_algebraMap]`. Establish `hc` using `congrArg (fun x : A => (x : Ω)) hk`. Establish `e : ∀ (p : ℤ[X]) (x : A), ((aeval x p : A) : Ω) = aeval (x : Ω) p`. Introduce `p x`.

Conclude with `(aeval_algebraMap_apply Ω x p).symm`. Move the coercions through the operations in `at hc`. Rewrite `hc` using `[e, e, e]`. Establish `hβ0 : (b : Ω) = β` using `rfl`. Establish `hβ1 : (b' : Ω) = β'` using `rfl`.

Rewrite `hc` using `[hβ0, hβ1, h0, h0']`. Establish `hne' : β' - β ≠ 0` using `sub_ne_zero.mpr (Ne.symm hne)`. Establish `hD : aeval β (derivative f) = -((k : Ω) * (β' - β))`. Establish `: (β' - β) * (aeval β (derivative f) + (k : Ω) * (β' - β)) = 0` using `by linear_combination -hc`. Use `(mul_eq_zero.mp this).resolve_left hne'` as an intermediate fact.

Take the linear combination `this`. Apply `hd` to reduce the goal to its premises. Rewrite using `[hD, Valuation.map_neg, Valuation.map_mul, Valuation.map_sub_swap]`. Establish `hk1 : A.valuation (k : Ω) ≤ 1` using `(A.valuation_le_one_iff _).mpr k.2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_of_root_congr_of_deriv_unit {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (f : Polynomial ℤ) (β β' : Ω)
    (hβ : A.valuation β ≤ 1) (hβ' : A.valuation β' ≤ 1) (h0 : Polynomial.aeval β f = 0) (h0' : Polynomial.aeval β' f = 0)
    (hd : ¬ A.valuation (Polynomial.aeval β (Polynomial.derivative f)) < 1) (hs : A.valuation (β - β') < 1) : β = β' := by
  by_contra hne
  have hb : β ∈ A := (A.valuation_le_one_iff β).mp hβ
  have hb' : β' ∈ A := (A.valuation_le_one_iff β').mp hβ'
  set b : A := ⟨β, hb⟩
  set b' : A := ⟨β', hb'⟩
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (f.map (algebraMap ℤ A)) b (b' - b)
  rw [add_sub_cancel, derivative_map, eval_map_algebraMap, eval_map_algebraMap, eval_map_algebraMap] at hk
  have hc := congrArg (fun x : A => (x : Ω)) hk
  have e : ∀ (p : ℤ[X]) (x : A), ((aeval x p : A) : Ω) = aeval (x : Ω) p := by
    intro p x
    exact (aeval_algebraMap_apply Ω x p).symm
  push_cast at hc
  rw [e, e, e] at hc
  have hβ0 : (b : Ω) = β := rfl
  have hβ1 : (b' : Ω) = β' := rfl
  rw [hβ0, hβ1, h0, h0'] at hc
  have hne' : β' - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hD : aeval β (derivative f) = -((k : Ω) * (β' - β)) := by
    have : (β' - β) * (aeval β (derivative f) + (k : Ω) * (β' - β)) = 0 := by linear_combination -hc
    have := (mul_eq_zero.mp this).resolve_left hne'
    linear_combination this
  apply hd
  rw [hD, Valuation.map_neg, Valuation.map_mul, Valuation.map_sub_swap]
  have hk1 : A.valuation (k : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr k.2
  calc A.valuation (k : Ω) * A.valuation (β - β') ≤ 1 * A.valuation (β - β') := by gcongr
    _ = A.valuation (β - β') := one_mul _
    _ < 1 := hs

end GlobalTheory
