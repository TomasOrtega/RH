import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMeanVol
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set

noncomputable section

namespace SphereMeanLinearBall

/- English proof (translation)
Simplify using `[HermNorm.norm, HermNorm.std]`.
-/
theorem std_norm (n : ℕ) (v : Fin n → ℂ) : (HermNorm.std n).norm v = √(∑ j, ‖v j‖ ^ 2) := by
  simp [HermNorm.norm, HermNorm.std]

/- English proof (translation)
Simplify using `[HermNorm.dualNorm, HermNorm.std]`.
-/
theorem std_dualNorm (n : ℕ) (y : Fin n → ℂ) :
    (HermNorm.std n).dualNorm y = √(∑ j, ‖y j‖ ^ 2) := by
  simp [HermNorm.dualNorm, HermNorm.std]

/- English proof (translation)
Establish `hS : 0 ≤ ∑ j, ‖w j‖ ^ 2` using `Finset.sum_nonneg fun _ _ => sq_nonneg _`. Establish `e : ∀ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2 = (∑ j, ‖w j‖ ^ 2)⁻¹ * ‖w j‖ ^ 2`. Introduce `j`. Rewrite using `[nrmv, std_norm, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt hS]`. Rewrite using `[Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum]`.

Break down `eq_or_ne (∑ j, ‖w j‖ ^ 2) 0 with h | h` into its components or cases. Simplify using `[h]`. Rewrite using `[inv_mul_cancel₀ h]`.
-/
theorem sum_sq_nrmv_le (n : ℕ) (w : Fin n → ℂ) :
    ∑ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2 ≤ 1 := by
  have hS : 0 ≤ ∑ j, ‖w j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have e : ∀ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2 = (∑ j, ‖w j‖ ^ 2)⁻¹ * ‖w j‖ ^ 2 := by
    intro j
    rw [nrmv, std_norm, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt hS]
  rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum]
  rcases eq_or_ne (∑ j, ‖w j‖ ^ 2) 0 with h | h
  · simp [h]
  · rw [inv_mul_cancel₀ h]

/- English proof (translation)
Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Repeatedly rewrite using `[norm_mul]`. Conclude with `Real.sum_mul_le_sqrt_mul_sqrt _ _ _`.
-/
theorem norm_sum_mul_le (n : ℕ) (a b : Fin n → ℂ) :
    ‖∑ j, a j * b j‖ ≤ √(∑ j, ‖a j‖ ^ 2) * √(∑ j, ‖b j‖ ^ 2) := by
  refine (norm_sum_le _ _).trans ?_
  simp_rw [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/- English proof (translation)
Use `lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) fun h => hy ?_` and prove the remaining obligations. Establish `h0` using `(Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ‖y j‖).mp h.symm`. Use function extensionality and compare the values at `j`. Simplify using `using h0 j (Finset.mem_univ j)`.
-/
theorem sum_sq_pos {n : ℕ} {y : Fin n → ℂ} (hy : y ≠ 0) : 0 < ∑ j, ‖y j‖ ^ 2 := by
  refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) fun h => hy ?_
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ‖y j‖).mp h.symm
  funext j
  simpa using h0 j (Finset.mem_univ j)

/- English proof (translation)
Rewrite using `[fsLog, std_dualNorm]`. Use `Real.log_nonpos (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) ?_` and prove the remaining obligations. Use `div_le_one_of_le₀ ?_ (Real.sqrt_nonneg _)` and prove the remaining obligations. Use `(norm_sum_mul_le n _ _).trans ?_` and prove the remaining obligations. Establish `h1 : √(∑ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2) ≤ 1`.

Rewrite using `[Real.sqrt_le_one]`. Conclude with `sum_sq_nrmv_le n w`. Conclude with `mul_le_of_le_one_left (Real.sqrt_nonneg _) h1`.
-/
theorem fsLog_nrmv_nonpos (n : ℕ) (y w : Fin n → ℂ) :
    fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y ≤ 0 := by
  rw [fsLog, std_dualNorm]
  refine Real.log_nonpos (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) ?_
  refine div_le_one_of_le₀ ?_ (Real.sqrt_nonneg _)
  refine (norm_sum_mul_le n _ _).trans ?_
  have h1 : √(∑ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact sum_sq_nrmv_le n w
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) h1

end SphereMeanLinearBall

open SphereMeanLinearBall in

/- English proof (translation)
Introduce `n y hy`. Use `set g : (Fin n → ℂ) → ℝ := fun w => fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y with hg`. Establish `hpos` using `sum_sq_pos hy`. Use `set r : ℝ := √(∑ j, ‖y j‖ ^ 2) with hr`. Establish `hr0 : 0 < r` using `Real.sqrt_pos.mpr hpos`.

Set `p : Fin n → ℂ` to `fun j => ((r : ℂ))⁻¹ * star (y j)`. Establish `hp : ∑ j, ‖p j‖ ^ 2 = 1`. Establish `e : ∀ j, ‖p j‖ ^ 2 = (∑ j, ‖y j‖ ^ 2)⁻¹ * ‖y j‖ ^ 2`. Introduce `j`. Use `show ‖((r : ℂ))⁻¹ * star (y j)‖ ^ 2 = _`.

Rewrite using `[norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr0.le, norm_star, mul_pow, inv_pow, hr, Real.sq_sqrt hpos.le]`. Rewrite using `[Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum, inv_mul_cancel₀ hpos.ne']`. Establish `hkey : ∀ a : Fin n → ℂ, Real.log ‖∑ j, a j * star (p j)‖ = fsLog (HermNorm.std n) a y`. Introduce `a`. Establish `e : ∑ j, a j * star (p j) = ((r : ℂ))⁻¹ * ∑ j, a j * y j`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [p, star_mul', star_inv₀, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, fsLog, std_dualNorm, ← hr, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr0.le, div_eq_inv_mul]`.

Set `e` to `(Equiv.uniqueProd (Fin n) (Fin 1)).symm`. Set `L1 : (Fin 1 × Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ)` to `(LinearEquiv.funCongrLeft ℝ ℂ e).toContinuousLinearEquiv`. Establish `hL1 : ∀ u, (fun j => u (0, j)) = L1 u`. Introduce `u`. Use function extensionality and compare the values at `j`.

Simplify using `[L1, e]`. Establish `hS : {u : Fin 1 × Fin n → ℂ | ∀ i, (HermNorm.std n).norm (fun j => u (i, j)) < 1} = L1 ⁻¹' ballH (HermNorm.std n)`. Use extensionality with `u`. Simplify using `only [mem_ofPred_eq, mem_preimage, ballH, Fin.forall_fin_one, hL1]`. Establish `hmean : ⨍ w in ballH (HermNorm.std n), g w = -(harmonic (n - 1) : ℝ) / 2`.

Rewrite using `[← h1 n p hp, sphereMean, hS, ← SphereMean.setAverage_comp_linearEquiv volume volume L1 (ballH (HermNorm.std n)) g]`. Use `congr 1`. Use function extensionality and compare the values at `u`. Rewrite using `[hkey]`. Simplify using `only [hg]`.

Rewrite using `[← hL1 u]`. Both sides reduce to the same expression. Use `⟨?_, fun w => fsLog_nrmv_nonpos n y w, hmean⟩` and prove the remaining obligations. Break down `eq_or_ne (harmonic (n - 1)) 0 with hH | hH` into its components or cases. Establish `hn1 : n - 1 = 0`.

Assume the negation of the conclusion as `hne`. Conclude with `(harmonic_pos hne).ne' hH`. Establish `hn : n = 1`. Break down `Nat.eq_zero_or_pos n with h0 | h0` into its components or cases. Substitute `h0` using the available equality.

Conclude with `absurd (Subsingleton.elim y 0) hy`. Use linear arithmetic over natural numbers and integers. Substitute `hn` using the available equality. Establish `hz : g = 0`. Use function extensionality and compare the values at `w`.

Simplify using `only [hg, Pi.zero_apply, fsLog, std_dualNorm, nrmv, std_norm, Fin.sum_univ_one]`. Rewrite using `[Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _), norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]`. Establish `hy0 : y 0 ≠ 0` using `fun h => hy (funext fun j => by rw [Subsingleton.elim j 0, h]; rfl)`. Break down `eq_or_ne (w 0) 0 with hw | hw` into its components or cases. Simplify using `[hw]`.

Rewrite using `[inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw), one_mul, div_self (norm_ne_zero_iff.mpr hy0), Real.log_one]`. Rewrite using `[hz]`. Conclude with `integrableOn_zero`. Assume the negation of the conclusion as `hni`. Establish `h0 : ⨍ w in ballH (HermNorm.std n), g w = 0`.

Rewrite using `[setAverage_eq, integral_undef hni, smul_zero]`. Rewrite `h0` using `[hmean]`. Conclude with `hH (by exact_mod_cast (by linarith : (harmonic (n - 1) : ℝ) = 0))`.
-/
theorem SphereMeanLinearBall.proof (h1 : SphereMeanLinear.Statement) : SphereMeanLinearBall.Statement := by
  intro n y hy
  set g : (Fin n → ℂ) → ℝ := fun w => fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y with hg
  have hpos := sum_sq_pos hy
  set r : ℝ := √(∑ j, ‖y j‖ ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hpos

  let p : Fin n → ℂ := fun j => ((r : ℂ))⁻¹ * star (y j)
  have hp : ∑ j, ‖p j‖ ^ 2 = 1 := by
    have e : ∀ j, ‖p j‖ ^ 2 = (∑ j, ‖y j‖ ^ 2)⁻¹ * ‖y j‖ ^ 2 := by
      intro j
      show ‖((r : ℂ))⁻¹ * star (y j)‖ ^ 2 = _
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr0.le, norm_star, mul_pow,
        inv_pow, hr, Real.sq_sqrt hpos.le]
    rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum, inv_mul_cancel₀ hpos.ne']
  have hkey : ∀ a : Fin n → ℂ, Real.log ‖∑ j, a j * star (p j)‖ = fsLog (HermNorm.std n) a y := by
    intro a
    have e : ∑ j, a j * star (p j) = ((r : ℂ))⁻¹ * ∑ j, a j * y j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [p, star_mul', star_inv₀, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
      ring
    rw [e, fsLog, std_dualNorm, ← hr, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hr0.le, div_eq_inv_mul]

  let e := (Equiv.uniqueProd (Fin n) (Fin 1)).symm
  let L1 : (Fin 1 × Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ) :=
    (LinearEquiv.funCongrLeft ℝ ℂ e).toContinuousLinearEquiv
  have hL1 : ∀ u, (fun j => u (0, j)) = L1 u := by
    intro u
    funext j
    simp [L1, e]
  have hS : {u : Fin 1 × Fin n → ℂ | ∀ i, (HermNorm.std n).norm (fun j => u (i, j)) < 1} =
      L1 ⁻¹' ballH (HermNorm.std n) := by
    ext u
    simp only [mem_ofPred_eq, mem_preimage, ballH, Fin.forall_fin_one, hL1]
  have hmean : ⨍ w in ballH (HermNorm.std n), g w = -(harmonic (n - 1) : ℝ) / 2 := by
    rw [← h1 n p hp, sphereMean, hS,
      ← SphereMean.setAverage_comp_linearEquiv volume volume L1 (ballH (HermNorm.std n)) g]
    congr 1
    funext u
    rw [hkey]
    simp only [hg]
    rw [← hL1 u]
    rfl
  refine ⟨?_, fun w => fsLog_nrmv_nonpos n y w, hmean⟩
  rcases eq_or_ne (harmonic (n - 1)) 0 with hH | hH
  ·
    have hn1 : n - 1 = 0 := by
      by_contra hne
      exact (harmonic_pos hne).ne' hH
    have hn : n = 1 := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        exact absurd (Subsingleton.elim y 0) hy
      · omega
    subst hn
    have hz : g = 0 := by
      funext w
      simp only [hg, Pi.zero_apply, fsLog, std_dualNorm, nrmv, std_norm, Fin.sum_univ_one]
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _), norm_mul, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
      have hy0 : y 0 ≠ 0 := fun h => hy (funext fun j => by rw [Subsingleton.elim j 0, h]; rfl)
      rcases eq_or_ne (w 0) 0 with hw | hw
      · simp [hw]
      · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw), one_mul,
          div_self (norm_ne_zero_iff.mpr hy0), Real.log_one]
    rw [hz]
    exact integrableOn_zero
  ·
    by_contra hni
    have h0 : ⨍ w in ballH (HermNorm.std n), g w = 0 := by
      rw [setAverage_eq, integral_undef hni, smul_zero]
    rw [hmean] at h0
    exact hH (by exact_mod_cast (by linarith : (harmonic (n - 1) : ℝ) = 0))

end

end GroundTheory.Heights₂.Heights
