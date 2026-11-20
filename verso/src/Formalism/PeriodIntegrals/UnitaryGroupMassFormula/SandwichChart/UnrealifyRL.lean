import Mathlib
import Formalism.PeriodIntegrals.LongWeylElementSquare
import Formalism.PeriodIntegrals.SwSand
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.SandwichOfOfCharts

noncomputable section

open Matrix Filter Topology Classical
open scoped ENNReal NNReal

namespace PI.SwSandwichOfWork

open PI.SwBig PI.SwSand

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

variable {k r : ℕ}

/- English proof (translation)
Introduce `k r X`. Rewrite using `[EuclideanSpace.norm_eq, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]`. Use `congr 1`. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_bool, Real.rpow_two, Complex.sq_norm, Complex.normSq_apply]`. Simplify using `[RL, realifyFun]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normRL : NormRL := by
  intro k r X
  rw [EuclideanSpace.norm_eq, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Real.rpow_two, Complex.sq_norm, Complex.normSq_apply]
  simp [RL, realifyFun]
  ring

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [unrealify, RL, realifyFun]`.
-/
theorem unrealify_RL (X : Mat k r) : unrealify (RL X) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, RL, realifyFun]

def sgI (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

/- English proof (translation)
Break down `i with ⟨i, hi⟩` into its components or cases. Break down `j with ⟨j, hj⟩` into its components or cases. Unfold `Hpk sgI`. Apply the tactic sequence `split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk] at *) <;> first | rfl | (exfalso; omega)`.
-/
theorem Log_Hpk_eq (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sgI k r i then (if i.val = r + k then -1 else 1) else 0 := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  unfold Hpk sgI
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk] at *) <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Unfold `sgI`. Apply the tactic sequence `split_ifs <;> simp_all [Fin.ext_iff] <;> omega`.
-/
theorem Log_sgI_sgI (i : Fin (2 * r + k + 1)) : sgI k r (sgI k r i) = i := by
  unfold sgI
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

/- English proof (translation)
Unfold `sgI`. Apply the tactic sequence `split_ifs <;> simp_all <;> omega`.
-/
theorem Log_sgI_val (i : Fin (2 * r + k + 1)) : ((sgI k r i).val = r + k ↔ i.val = r + k) := by
  unfold sgI
  split_ifs <;> simp_all <;> omega

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (sgI k r i)]`. Rewrite using `[Log_Hpk_eq, Log_Hpk_eq, if_pos rfl, Log_sgI_sgI, Matrix.one_apply]`. Establish `hv` using `(Log_sgI_val (k := k) (r := r) i)`. Distinguish the cases in `h : j = i`.

Substitute `h` using the available equality. Distinguish the cases in `h2 : j.val = r + k`. Rewrite using `[if_pos h2, if_pos rfl, if_pos (hv.2 h2), if_pos rfl]`. Evaluate the numerical expressions. Rewrite using `[if_neg h2, if_pos rfl, if_neg (fun h' => h2 (hv.1 h')), if_pos rfl]`.

Evaluate the numerical expressions. Rewrite using `[if_neg h, if_neg (Ne.symm h), mul_zero]`. Introduce `l _ hl`. Rewrite using `[Log_Hpk_eq, if_neg hl, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (sgI k r i)]
  · rw [Log_Hpk_eq, Log_Hpk_eq, if_pos rfl, Log_sgI_sgI, Matrix.one_apply]
    have hv := (Log_sgI_val (k := k) (r := r) i)
    by_cases h : j = i
    · subst h
      by_cases h2 : j.val = r + k
      · rw [if_pos h2, if_pos rfl, if_pos (hv.2 h2), if_pos rfl]; norm_num
      · rw [if_neg h2, if_pos rfl, if_neg (fun h' => h2 (hv.1 h')), if_pos rfl]; norm_num
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
  · intro l _ hl; rw [Log_Hpk_eq, if_neg hl, zero_mul]
  · simp

/- English proof (translation)
Introduce `k r`. Establish `hE : HasStrictFDerivAt (NormedSpace.exp : Mat k r → Mat k r) ((ContinuousLinearEquiv.refl ℝ (Mat k r) : Mat k r →L[ℝ] Mat k r)) 0`. Rewrite using `[ContinuousLinearEquiv.coe_refl]`. Conclude with `hasStrictFDerivAt_exp_zero`. Take `⟨ε, hε, hleft⟩` from `Metric.eventually_nhds_iff.1 hE.eventually_left_inverse`.

Use `set H := Hpk k r`. Establish `hHH : H * H = 1` using `hpk_sq`. Establish `hHu : IsUnit H` using `(Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hHH)`. Establish `hHi : H⁻¹ = H` using `Matrix.inv_eq_right_inv hHH`. Use `set C := ‖H‖ * ‖H‖ + 1`.

Establish `hC : 0 < C` using `by positivity`. Use `⟨min ε (ε / C), lt_min hε (div_pos hε hC), fun L hL hG => ?_⟩` and prove the remaining obligations. Establish `hLε : ‖L‖ < ε` using `lt_of_lt_of_le hL (min_le_left _ _)`. Establish `hLC : ‖L‖ < ε / C` using `lt_of_lt_of_le hL (min_le_right _ _)`. Establish `hadj : ‖adjH L‖ < ε`.

Establish `h1 : ‖adjH L‖ ≤ ‖H‖ * ‖H‖ * ‖L‖`. Unfold `adjH`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ‖H‖ * ‖H‖ * ‖L‖ < ε`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hexp : NormedSpace.exp (adjH L) = NormedSpace.exp (-L)`. Establish `hG' : (NormedSpace.exp L)ᴴ * H * NormedSpace.exp L = H` using `hG`. Establish `h1 : NormedSpace.exp (adjH L) = H * (NormedSpace.exp L)ᴴ * H`. Use `Matrix.exp_conj H Lᴴ hHu` as an intermediate fact.

Rewrite `this` using `[hHi, Matrix.exp_conjTranspose]`. Conclude with `this`. Establish `h2 : (H * (NormedSpace.exp L)ᴴ * H) * NormedSpace.exp L = 1`. Rewrite using `[Matrix.mul_assoc (H * _), show H * (NormedSpace.exp L)ᴴ * (H * NormedSpace.exp L) = H * ((NormedSpace.exp L)ᴴ * H * NormedSpace.exp L) by simp only [Matrix.mul_assoc], hG', hHH]`. Rewrite using `[h1, Matrix.exp_neg, Matrix.inv_eq_left_inv h2]`.

Establish `e1` using `hleft (y := adjH L) (by simpa using hadj)`. Establish `e2` using `hleft (y := -L) (by simpa using hLε)`. Rewrite `e1` using `[hexp]`. Use `show adjH L + L = 0`. Rewrite using `[← e1, e2, neg_add_cancel]`.
-/
theorem logG : LogG := by
  intro k r
  have hE : HasStrictFDerivAt (NormedSpace.exp : Mat k r → Mat k r)
      ((ContinuousLinearEquiv.refl ℝ (Mat k r) : Mat k r →L[ℝ] Mat k r)) 0 := by
    rw [ContinuousLinearEquiv.coe_refl]
    exact hasStrictFDerivAt_exp_zero
  obtain ⟨ε, hε, hleft⟩ := Metric.eventually_nhds_iff.1 hE.eventually_left_inverse
  set H := Hpk k r
  have hHH : H * H = 1 := hpk_sq
  have hHu : IsUnit H := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hHH)
  have hHi : H⁻¹ = H := Matrix.inv_eq_right_inv hHH
  set C := ‖H‖ * ‖H‖ + 1
  have hC : 0 < C := by positivity
  refine ⟨min ε (ε / C), lt_min hε (div_pos hε hC), fun L hL hG => ?_⟩
  have hLε : ‖L‖ < ε := lt_of_lt_of_le hL (min_le_left _ _)
  have hLC : ‖L‖ < ε / C := lt_of_lt_of_le hL (min_le_right _ _)
  have hadj : ‖adjH L‖ < ε := by
    have h1 : ‖adjH L‖ ≤ ‖H‖ * ‖H‖ * ‖L‖ := by
      unfold adjH
      calc ‖H * Lᴴ * H‖ ≤ ‖H * Lᴴ‖ * ‖H‖ := norm_mul_le _ _
        _ ≤ ‖H‖ * ‖Lᴴ‖ * ‖H‖ := by gcongr; exact norm_mul_le _ _
        _ = ‖H‖ * ‖H‖ * ‖L‖ := by rw [Matrix.frobenius_norm_conjTranspose]; ring
    have h2 : ‖H‖ * ‖H‖ * ‖L‖ < ε := by
      calc ‖H‖ * ‖H‖ * ‖L‖ ≤ C * ‖L‖ := by gcongr; simp [C]
        _ < C * (ε / C) := by gcongr
        _ = ε := by field_simp
    linarith
  have hexp : NormedSpace.exp (adjH L) = NormedSpace.exp (-L) := by
    have hG' : (NormedSpace.exp L)ᴴ * H * NormedSpace.exp L = H := hG
    have h1 : NormedSpace.exp (adjH L) = H * (NormedSpace.exp L)ᴴ * H := by
      have := Matrix.exp_conj H Lᴴ hHu
      rw [hHi, Matrix.exp_conjTranspose] at this
      exact this
    have h2 : (H * (NormedSpace.exp L)ᴴ * H) * NormedSpace.exp L = 1 := by
      rw [Matrix.mul_assoc (H * _), show H * (NormedSpace.exp L)ᴴ * (H * NormedSpace.exp L)
        = H * ((NormedSpace.exp L)ᴴ * H * NormedSpace.exp L) by simp only [Matrix.mul_assoc], hG', hHH]
    rw [h1, Matrix.exp_neg, Matrix.inv_eq_left_inv h2]
  have e1 := hleft (y := adjH L) (by simpa using hadj)
  have e2 := hleft (y := -L) (by simpa using hLε)
  rw [hexp] at e1
  show adjH L + L = 0
  rw [← e1, e2, neg_add_cancel]

end PI.SwSandwichOfWork
