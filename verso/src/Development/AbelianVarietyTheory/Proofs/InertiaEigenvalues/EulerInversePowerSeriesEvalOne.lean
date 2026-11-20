import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet

noncomputable section

namespace GlobalTheory.JSW

open PowerSeries

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Simplify `hp.add hq` using `[Polynomial.coe_add, mul_add, Polynomial.eval_add]`. Consider the case `monomial n a`. Establish `hf : (fun d => coeff d (mk c * ((Polynomial.monomial n a : Polynomial ℂ) : PowerSeries ℂ))) = fun d => if n ≤ d then c (d - n) * a else 0`.

Use function extensionality and compare the values at `d`. Rewrite using `[Polynomial.coe_monomial, PowerSeries.monomial_eq_C_mul_X_pow, ← mul_assoc, PowerSeries.coeff_mul_X_pow']`. Apply the tactic sequence `split_ifs <;> simp [PowerSeries.coeff_mul_C]`. Rewrite using `[hf, Polynomial.eval_monomial, one_pow, mul_one]`. Use `(hasSum_nat_add_iff' n).mp ?_` and prove the remaining obligations.

Establish `h0 : ∑ i ∈ Finset.range n, (if n ≤ i then c (i - n) * a else 0) = 0`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_range]`. Simplify using `[not_le.mpr hi]`. Rewrite using `[h0, sub_zero]`.

Simplify using `using (Summable.of_norm hc).hasSum.mul_right a`.
-/
theorem hasSum_coeff_mk_mul_polynomial (c : ℕ → ℂ) (hc : Summable fun d => ‖c d‖)
    (p : Polynomial ℂ) :
    HasSum (fun d => coeff d (mk c * (p : PowerSeries ℂ))) ((∑' d, c d) * p.eval 1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa [Polynomial.coe_add, mul_add, Polynomial.eval_add] using hp.add hq
  | monomial n a =>
    have hf : (fun d => coeff d (mk c * ((Polynomial.monomial n a : Polynomial ℂ) : PowerSeries ℂ)))
        = fun d => if n ≤ d then c (d - n) * a else 0 := by
      funext d
      rw [Polynomial.coe_monomial, PowerSeries.monomial_eq_C_mul_X_pow, ← mul_assoc,
        PowerSeries.coeff_mul_X_pow']
      split_ifs <;> simp [PowerSeries.coeff_mul_C]
    rw [hf, Polynomial.eval_monomial, one_pow, mul_one]
    refine (hasSum_nat_add_iff' n).mp ?_
    have h0 : ∑ i ∈ Finset.range n, (if n ≤ i then c (i - n) * a else 0) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_range] at hi
      simp [not_le.mpr hi]
    rw [h0, sub_zero]
    simpa using (Summable.of_norm hc).hasSum.mul_right a

/- English proof (translation)
Use `set P : Polynomial ℂ := ∏ p, (1 - Polynomial.C (Q p) * Polynomial.X) with hPdef`. Establish `hP : (P : PowerSeries ℂ) = ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X)`. Use `map_prod (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ) (fun p => 1 - Polynomial.C (Q p) * Polynomial.X) Finset.univ` as an intermediate fact. Rewrite using `[hPdef]`. Simplify using `only [Polynomial.coeToPowerSeries.ringHom_apply] at this`.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `h1` using `hasSum_coeff_mk_mul_polynomial c hc P`. Rewrite `h1` using `[hP, h]`. Establish `h2 : HasSum (fun d => coeff d (1 : PowerSeries ℂ)) 1`.

Simplify `hasSum_ite_eq 0 (1 : ℂ)` using `[PowerSeries.coeff_one]`. Establish `h3` using `h1.unique h2`. Establish `hev : P.eval 1 = ∏ p, (1 - Q p)` using `by simp [hPdef, Polynomial.eval_prod]`. Rewrite `h3` using `[hev]`. Use `⟨fun h0 => ?_, ?_⟩` and prove the remaining obligations.

Rewrite `h3` using `[h0, mul_zero]`. Conclude with `zero_ne_one h3`. Rewrite using `[← eq_inv_of_mul_eq_one_left h3]`. Conclude with `(Summable.of_norm hc).hasSum`.
-/
theorem eulerInverse_eval_one {ι : Type} [Fintype ι] (c : ℕ → ℂ) (hc : Summable fun d => ‖c d‖)
    (Q : ι → ℂ)
    (h : PowerSeries.mk c * ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X) = 1) :
    (∏ p, (1 - Q p)) ≠ 0 ∧ HasSum c (∏ p, (1 - Q p))⁻¹ := by
  set P : Polynomial ℂ := ∏ p, (1 - Polynomial.C (Q p) * Polynomial.X) with hPdef
  have hP : (P : PowerSeries ℂ) = ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X) := by
    have := map_prod (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ)
      (fun p => 1 - Polynomial.C (Q p) * Polynomial.X) Finset.univ
    rw [hPdef]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply] at this
    rw [this]
    simp
  have h1 := hasSum_coeff_mk_mul_polynomial c hc P
  rw [hP, h] at h1
  have h2 : HasSum (fun d => coeff d (1 : PowerSeries ℂ)) 1 := by
    simpa [PowerSeries.coeff_one] using hasSum_ite_eq 0 (1 : ℂ)
  have h3 := h1.unique h2
  have hev : P.eval 1 = ∏ p, (1 - Q p) := by simp [hPdef, Polynomial.eval_prod]
  rw [hev] at h3
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, mul_zero] at h3
    exact zero_ne_one h3
  · rw [← eq_inv_of_mul_eq_one_left h3]
    exact (Summable.of_norm hc).hasSum

/- English proof (translation)
Introduce `c hc Q h` and use `eulerInverse_eval_one c hc Q h`.
-/
example : ∀ {ι : Type} [Fintype ι] (c : ℕ → ℂ), (Summable fun d => ‖c d‖) → ∀ (Q : ι → ℂ),
    PowerSeries.mk c * ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X) = 1 →
    (∏ p, (1 - Q p)) ≠ 0 ∧ HasSum c (∏ p, (1 - Q p))⁻¹ :=
  fun c hc Q h => eulerInverse_eval_one c hc Q h

end GlobalTheory.JSW
