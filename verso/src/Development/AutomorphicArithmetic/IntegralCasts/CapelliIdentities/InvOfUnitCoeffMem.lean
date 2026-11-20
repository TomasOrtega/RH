import Mathlib

/- English proof (translation)
Introduce `R _ S f hf _ n`. Establish `h1 : ((1⁻¹ : Rˣ) : R) ∈ S`. Rewrite using `[inv_one, Units.val_one]`. Conclude with `S.one_mem`. Proceed by induction on `n using Nat.strong_induction_on with`.

Consider the case `_ n ih`. Rewrite using `[PowerSeries.coeff_invOfUnit]`. Use `split_ifs with hn`. Conclude with `h1`. Use `S.mul_mem (S.neg_mem h1) (S.sum_mem fun x _ => ?_) split_ifs with hx` and prove the remaining obligations.

Conclude with `S.mul_mem (hf _) (ih _ hx)`. Conclude with `S.zero_mem`.
-/
theorem UpperTheory.invOfUnit_coeff_mem :
    ∀ (R : Type) [CommRing R] (S : Subring R) (f : PowerSeries R), (∀ n, PowerSeries.coeff n f ∈ S) → PowerSeries.constantCoeff f = 1 → ∀ n, PowerSeries.coeff n (PowerSeries.invOfUnit f 1) ∈ S := by
  intro R _ S f hf _ n
  have h1 : ((1⁻¹ : Rˣ) : R) ∈ S := by
    rw [inv_one, Units.val_one]
    exact S.one_mem
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_invOfUnit]
    split_ifs with hn
    · exact h1
    · refine S.mul_mem (S.neg_mem h1) (S.sum_mem fun x _ => ?_)
      split_ifs with hx
      · exact S.mul_mem (hf _) (ih _ hx)
      · exact S.zero_mem
