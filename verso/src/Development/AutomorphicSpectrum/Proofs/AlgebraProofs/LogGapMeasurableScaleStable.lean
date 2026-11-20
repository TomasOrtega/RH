import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable

set_option maxSynthPendingDepth 1

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

noncomputable section

variable {n : ℕ}

/- English proof (translation)
Establish `hp : Continuous (fun y : EuclideanSpace ℂ (Fin n) => h.pointOf y)`. Unfold `HermNorm.pointOf`. Use `fun_prop`. Conclude with `continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp hp)`.
-/
theorem continuous_pairing_pointOf (h : HermNorm n) (u : Fin n → ℂ) :
    Continuous fun y : EuclideanSpace ℂ (Fin n) => ∑ j, u j * h.pointOf y j := by
  have hp : Continuous (fun y : EuclideanSpace ℂ (Fin n) => h.pointOf y) := by
    unfold HermNorm.pointOf; fun_prop
  exact continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp hp)

/- English proof (translation)
Establish `hpt : h.pointOf (t • y) = t • h.pointOf y`. Simplify using `only [HermNorm.pointOf]`. Rewrite using `[← Matrix.mulVec_smul]`. Use `congr 1`. Rewrite using `[hpt, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring`.
-/
theorem pairing_pointOf_smul (h : HermNorm n) (u : Fin n → ℂ) (t : ℂ)
    (y : EuclideanSpace ℂ (Fin n)) :
    ∑ j, u j * h.pointOf (t • y) j = t * ∑ j, u j * h.pointOf y j := by
  have hpt : h.pointOf (t • y) = t • h.pointOf y := by
    simp only [HermNorm.pointOf]
    rw [← Matrix.mulVec_smul]
    congr 1
  rw [hpt, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

/- English proof (translation)
Establish `hA : IsUnit h.matᵀ.det` using `by rw [Matrix.det_transpose]; exact h.isUnit_det`. Rewrite using `[HermNorm.dualNorm, HermNorm.pointOf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec, EuclideanSpace.norm_eq]`.
-/
theorem dualNorm_pointOf_eq (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) :
    h.dualNorm (h.pointOf y) = ‖y‖ := by
  have hA : IsUnit h.matᵀ.det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  rw [HermNorm.dualNorm, HermNorm.pointOf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA,
    Matrix.one_mulVec, EuclideanSpace.norm_eq]

/- English proof (translation)
Establish `hne : h.mat *ᵥ u ≠ 0`. Introduce `h0`. Apply `hu` to reduce the goal to its premises. Establish `h1` using `congrArg (fun v => h.mat⁻¹ *ᵥ v) h0`. Simplify `h1` using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det]`.

Take `⟨i, hi⟩` from `Function.ne_iff.mp hne`. Rewrite using `[HermNorm.norm]`. Use `Real.sqrt_pos.mpr (Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, ?_⟩)` and prove the remaining obligations. Establish `: 0 < ‖(h.mat *ᵥ u) i‖` using `norm_pos_iff.mpr hi`. Check the signs of the components of the expression.
-/
theorem hermNorm_pos (h : HermNorm n) {u : Fin n → ℂ} (hu : u ≠ 0) : 0 < h.norm u := by
  have hne : h.mat *ᵥ u ≠ 0 := by
    intro h0
    apply hu
    have h1 := congrArg (fun v => h.mat⁻¹ *ᵥ v) h0
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det] using h1
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  rw [HermNorm.norm]
  refine Real.sqrt_pos.mpr (Finset.sum_pos' (fun _ _ => by positivity)
    ⟨i, Finset.mem_univ _, ?_⟩)
  have : 0 < ‖(h.mat *ᵥ u) i‖ := norm_pos_iff.mpr hi
  positivity

/- English proof (translation)
Establish `hN` using `hermNorm_pos h hu`. Unfold `logGap`. Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Simplify using `[HermNorm.pointOf]`.

Establish `hy' : 0 < ‖y‖` using `norm_pos_iff.mpr hy`. Establish `hc : 0 < Real.exp (-s.toReal) * h.norm u * ‖y‖` using `by positivity`. Distinguish the cases in `hp : ∑ j, u j * h.pointOf y j = 0`. Simplify using `[hy, hp, hs.lt_top, hc]`. Establish `hpn : 0 < ‖∑ j, u j * h.pointOf y j‖` using `norm_pos_iff.mpr hp`.

Rewrite using `[if_neg hy, if_neg hp, ENNReal.lt_ofReal_iff_toReal_lt hs, fsLog, dualNorm_pointOf_eq, Real.log_div hpn.ne' hy'.ne', ← Real.log_lt_log_iff hpn hc, Real.log_mul (by positivity) hy'.ne', Real.log_mul (Real.exp_pos _).ne' hN.ne', Real.log_exp]`. Apply the tactic sequence `constructor <;> intro hh <;> linarith`.
-/
theorem lt_logGap_iff (h : HermNorm n) {u : Fin n → ℂ} (hu : u ≠ 0) {s : ℝ≥0∞} (hs : s ≠ ⊤)
    (y : EuclideanSpace ℂ (Fin n)) :
    s < logGap h u y ↔
      ‖∑ j, u j * h.pointOf y j‖ < Real.exp (-s.toReal) * h.norm u * ‖y‖ := by
  have hN := hermNorm_pos h hu
  unfold logGap
  by_cases hy : y = 0
  · subst hy
    simp [HermNorm.pointOf]
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hc : 0 < Real.exp (-s.toReal) * h.norm u * ‖y‖ := by positivity
  by_cases hp : ∑ j, u j * h.pointOf y j = 0
  · simp [hy, hp, hs.lt_top, hc]
  · have hpn : 0 < ‖∑ j, u j * h.pointOf y j‖ := norm_pos_iff.mpr hp
    rw [if_neg hy, if_neg hp, ENNReal.lt_ofReal_iff_toReal_lt hs, fsLog, dualNorm_pointOf_eq,
      Real.log_div hpn.ne' hy'.ne', ← Real.log_lt_log_iff hpn hc,
      Real.log_mul (by positivity) hy'.ne', Real.log_mul (Real.exp_pos _).ne' hN.ne', Real.log_exp]
    constructor <;> intro hh <;> linarith

/- English proof (translation)
Unfold `logGap`. Distinguish the cases in `hy : y = 0`. Simplify using `[hy]`. Simplify using `[hy, hs.lt_top]`.
-/
theorem lt_logGap_zero_iff (h : HermNorm n) {s : ℝ≥0∞} (hs : s ≠ ⊤)
    (y : EuclideanSpace ℂ (Fin n)) : s < logGap h 0 y ↔ y ≠ 0 := by
  unfold logGap
  by_cases hy : y = 0
  · simp [hy]
  · simp [hy, hs.lt_top]

/- English proof (translation)
Use extensionality with `y`. Simplify using the standard rewrite rules.
-/
theorem logGap_levelSet_top (h : HermNorm n) (u : Fin n → ℂ) :
    {y | (⊤ : ℝ≥0∞) < logGap h u y} = ∅ := by
  ext y
  simp

/- English proof (translation)
Distinguish the cases in `hs : s = ⊤`. Substitute `hs` using the available equality. Rewrite using `[logGap_levelSet_top]`. Conclude with `⟨isOpen_empty, fun y hy => hy.elim⟩`. Distinguish the cases in `hu : u = 0`.

Substitute `hu` using the available equality. Establish `hset : {y | s < logGap h 0 y} = {y : EuclideanSpace ℂ (Fin n) | y ≠ 0}` using `Set.ext fun y => lt_logGap_zero_iff h hs y`. Rewrite using `[hset]`. Conclude with `⟨isOpen_ne, fun y hy t ht => smul_ne_zero ht hy⟩`. Establish `hset : {y | s < logGap h u y} = {y : EuclideanSpace ℂ (Fin n) | ‖∑ j, u j * h.pointOf y j‖ < Real.exp (-s.toReal) * h.norm u * ‖y‖}` using `Set.ext fun y => lt_logGap_iff h hu hs y`.

Rewrite using `[hset]`. Use `⟨isOpen_lt (continuous_pairing_pointOf h u).norm (continuous_const.mul continuous_norm), fun y hy t ht => ?_⟩` and prove the remaining obligations. Establish `ht' : 0 < ‖t‖` using `norm_pos_iff.mpr ht`. Establish `hy' : ‖∑ j, u j * h.pointOf y j‖ < Real.exp (-s.toReal) * h.norm u * ‖y‖` using `hy`. Use `show ‖∑ j, u j * h.pointOf (t • y) j‖ < Real.exp (-s.toReal) * h.norm u * ‖t • y‖`.

Rewrite using `[pairing_pointOf_smul, norm_mul, norm_smul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem logGap_levelSet (h : HermNorm n) (u : Fin n → ℂ) (s : ℝ≥0∞) :
    IsOpen {y | s < logGap h u y} ∧ IsScaleStable {y | s < logGap h u y} := by
  by_cases hs : s = ⊤
  · subst hs
    rw [logGap_levelSet_top]
    exact ⟨isOpen_empty, fun y hy => hy.elim⟩
  by_cases hu : u = 0
  · subst hu
    have hset : {y | s < logGap h 0 y} = {y : EuclideanSpace ℂ (Fin n) | y ≠ 0} :=
      Set.ext fun y => lt_logGap_zero_iff h hs y
    rw [hset]
    exact ⟨isOpen_ne, fun y hy t ht => smul_ne_zero ht hy⟩
  have hset : {y | s < logGap h u y} = {y : EuclideanSpace ℂ (Fin n) |
      ‖∑ j, u j * h.pointOf y j‖ < Real.exp (-s.toReal) * h.norm u * ‖y‖} :=
    Set.ext fun y => lt_logGap_iff h hu hs y
  rw [hset]
  refine ⟨isOpen_lt (continuous_pairing_pointOf h u).norm (continuous_const.mul continuous_norm),
    fun y hy t ht => ?_⟩
  have ht' : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hy' : ‖∑ j, u j * h.pointOf y j‖ < Real.exp (-s.toReal) * h.norm u * ‖y‖ := hy
  show ‖∑ j, u j * h.pointOf (t • y) j‖ < Real.exp (-s.toReal) * h.norm u * ‖t • y‖
  rw [pairing_pointOf_smul, norm_mul, norm_smul]
  calc ‖t‖ * ‖∑ j, u j * h.pointOf y j‖
      < ‖t‖ * (Real.exp (-s.toReal) * h.norm u * ‖y‖) := mul_lt_mul_of_pos_left hy' ht'
    _ = Real.exp (-s.toReal) * h.norm u * (‖t‖ * ‖y‖) := by ring

/- English proof (translation)
Introduce `n h u`. Conclude with `⟨measurable_of_Ioi fun s => (logGap_levelSet h u s).1.measurableSet, logGap_levelSet h u⟩`.
-/
theorem logGap_basic : ∀ (n : ℕ) (h : HermNorm n) (u : Fin n → ℂ),
    Measurable (logGap h u) ∧
      ∀ s : ℝ≥0∞, IsOpen {y | s < logGap h u y} ∧ IsScaleStable {y | s < logGap h u y} := by
  intro n h u
  exact ⟨measurable_of_Ioi fun s => (logGap_levelSet h u s).1.measurableSet,
    logGap_levelSet h u⟩

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
