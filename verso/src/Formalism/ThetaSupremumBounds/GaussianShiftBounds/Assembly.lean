import Mathlib
import Formalism.ThetaSupremumBounds.StatementC

open Finset
open scoped Real

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)

/- English proof (translation)
Introduce `Pl _ r g0 ν n Om Ksq kc Msq Th0sq hh hK hkc hM hT hhh hOm h`. Establish `hf : ∀ τ, Real.log ((Om τ)⁻¹ ^ n τ * (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * g0) * Real.exp (∑ i, ph (ν τ i)))) = ((∑ i, ph (ν τ i)) - (n τ : ℝ) * Real.log (Om τ)) + (1 + 2 * (g0 : ℝ) * Real.log (2 * (n τ : ℝ) + 2))`. Introduce `τ`. Establish `h2 : (0 : ℝ) < 2 * n τ + 2` using `by positivity`. Establish `h3` using `hOm τ`.

Rewrite using `[Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_inv, Real.log_exp, Real.log_exp]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : ∀ τ, 0 < (Om τ)⁻¹ ^ n τ * (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * g0) * Real.exp (∑ i, ph (ν τ i)))`. Introduce `τ`.

Establish `h3` using `hOm τ`. Check the signs of the components of the expression. Establish `hP : 0 < ∏ τ, ((Om τ)⁻¹ ^ n τ * (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * g0) * Real.exp (∑ i, ph (ν τ i))))` using `Finset.prod_pos (fun τ _ => hpos τ)`. Use `le_trans (Real.log_le_log hK h) (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Real.log_mul hhh.ne' (by positivity), Real.log_mul (by positivity) hP.ne', Real.log_prod (fun τ _ => (hpos τ).ne'), Finset.sum_congr rfl (fun τ _ => hf τ), Finset.sum_add_distrib, Real.log_mul (by positivity) hT.ne', Real.log_mul (by positivity) hM.ne', Real.log_pow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem size_at_embedding : SizeAtEmbedding := by
  intro Pl _ r g0 ν n Om Ksq kc Msq Th0sq hh hK hkc hM hT hhh hOm h
  have hf : ∀ τ, Real.log ((Om τ)⁻¹ ^ n τ *
      (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * g0) * Real.exp (∑ i, ph (ν τ i)))) =
      ((∑ i, ph (ν τ i)) - (n τ : ℝ) * Real.log (Om τ)) +
        (1 + 2 * (g0 : ℝ) * Real.log (2 * (n τ : ℝ) + 2)) := by
    intro τ
    have h2 : (0 : ℝ) < 2 * n τ + 2 := by positivity
    have h3 := hOm τ
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_inv,
      Real.log_exp, Real.log_exp]
    push_cast; ring
  have hpos : ∀ τ, 0 < (Om τ)⁻¹ ^ n τ *
      (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * g0) * Real.exp (∑ i, ph (ν τ i))) := by
    intro τ
    have h3 := hOm τ
    positivity
  have hP : 0 < ∏ τ, ((Om τ)⁻¹ ^ n τ *
      (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * g0) * Real.exp (∑ i, ph (ν τ i)))) :=
    Finset.prod_pos (fun τ _ => hpos τ)
  refine le_trans (Real.log_le_log hK h) (le_of_eq ?_)
  rw [Real.log_mul hhh.ne' (by positivity), Real.log_mul (by positivity) hP.ne',
    Real.log_prod (fun τ _ => (hpos τ).ne'), Finset.sum_congr rfl (fun τ _ => hf τ),
    Finset.sum_add_distrib, Real.log_mul (by positivity) hT.ne', Real.log_mul (by positivity) hM.ne',
    Real.log_pow]
  push_cast; ring

/- English proof (translation)
Introduce `d v rdE A1 Z LL0 p_power_smul_sub_sum logOmK logOm hd hv hrd hZ1 hZ2 hFE hK hOm`. Establish `hs : 0 < Real.sqrt d` using `Real.sqrt_pos.mpr hd`. Establish `hpi` using `Real.pi_pos`. Establish `e1 : Real.log (2 / Real.sqrt d) = Real.log 2 - Real.log d / 2`. Rewrite using `[Real.log_div (by norm_num) hs.ne', Real.log_sqrt hd.le]`.

Establish `e2 : Real.log (2 * π) = Real.log 2 + Real.log π` using `Real.log_mul (by norm_num) hpi.ne'`. Establish `e3 : Real.log (d / π) = Real.log d - Real.log π` using `Real.log_div hd.ne' hpi.ne'`. Establish `e4 : Real.log (2 * π / Real.sqrt d) = Real.log 2 + Real.log π - Real.log d / 2`. Rewrite using `[Real.log_div (by positivity) hs.ne', e2, Real.log_sqrt hd.le]`. Establish `e5 : Real.log (π / v) = Real.log π - Real.log v` using `Real.log_div hpi.ne' hv.ne'`.

Establish `e6 : Real.log rdE = Real.log 2 + Real.log v`. Rewrite using `[hrd, Real.log_mul (by norm_num) hv.ne']`. Establish `e7 : Real.log (Real.sqrt d) = Real.log d / 2` using `Real.log_sqrt hd.le`. Rewrite `hZ1` using `[e1]`. Rewrite `hZ2` using `[e2]`.

Rewrite `hFE` using `[e3]`. Rewrite `hOm` using `[e6, e7]`. Rewrite using `[e4, e5]`. Use `⟨by linarith, by linarith, by linarith⟩` and prove the remaining obligations.
-/
theorem period_value : PeriodValue := by
  intro d v rdE A1 Z LL0 p_power_smul_sub_sum logOmK logOm hd hv hrd hZ1 hZ2 hFE hK hOm
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hpi := Real.pi_pos
  have e1 : Real.log (2 / Real.sqrt d) = Real.log 2 - Real.log d / 2 := by
    rw [Real.log_div (by norm_num) hs.ne', Real.log_sqrt hd.le]
  have e2 : Real.log (2 * π) = Real.log 2 + Real.log π := Real.log_mul (by norm_num) hpi.ne'
  have e3 : Real.log (d / π) = Real.log d - Real.log π := Real.log_div hd.ne' hpi.ne'
  have e4 : Real.log (2 * π / Real.sqrt d) = Real.log 2 + Real.log π - Real.log d / 2 := by
    rw [Real.log_div (by positivity) hs.ne', e2, Real.log_sqrt hd.le]
  have e5 : Real.log (π / v) = Real.log π - Real.log v := Real.log_div hpi.ne' hv.ne'
  have e6 : Real.log rdE = Real.log 2 + Real.log v := by
    rw [hrd, Real.log_mul (by norm_num) hv.ne']
  have e7 : Real.log (Real.sqrt d) = Real.log d / 2 := Real.log_sqrt hd.le
  rw [e1] at hZ1; rw [e2] at hZ2; rw [e3] at hFE; rw [e6, e7] at hOm
  rw [e4, e5]
  refine ⟨by linarith, by linarith, by linarith⟩

end Formalism.DimensionVariation
