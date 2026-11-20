import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField Matrix

noncomputable section

variable {n : ℕ}

/- English proof (translation)
Establish `hinv : IsUnit h.matᵀ.det` using `by rw [det_transpose]; exact h.isUnit_det`. Establish `hpair : ∑ j, u j * y j = ∑ i, (h.mat *ᵥ u) i * ((h.matᵀ)⁻¹ *ᵥ y) i`. Establish `e1 : (∑ j, u j * y j) = u ⬝ᵥ y` using `rfl`. Establish `e2 : (∑ i, (h.mat *ᵥ u) i * ((h.matᵀ)⁻¹ *ᵥ y) i) = (h.mat *ᵥ u) ⬝ᵥ ((h.matᵀ)⁻¹ *ᵥ y)` using `rfl`. Rewrite using `[e1, e2, dotProduct_comm (h.mat *ᵥ u), dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, mul_nonsing_inv _ hinv, one_mulVec, dotProduct_comm]`.

Rewrite using `[hpair]`. Combine the equalities or inequalities in the displayed calculation. Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `_ ≤ √(∑ i, ‖(h.mat *ᵥ u) i‖ ^ 2) * √(∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _`.

Use `_ = h.norm u * h.dualNorm y := rfl`.
-/
theorem HermNorm.norm_pairing_le (h : HermNorm n) (u y : Fin n → ℂ) :
    ‖∑ j, u j * y j‖ ≤ h.norm u * h.dualNorm y := by
  have hinv : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  have hpair : ∑ j, u j * y j = ∑ i, (h.mat *ᵥ u) i * ((h.matᵀ)⁻¹ *ᵥ y) i := by
    have e1 : (∑ j, u j * y j) = u ⬝ᵥ y := rfl
    have e2 : (∑ i, (h.mat *ᵥ u) i * ((h.matᵀ)⁻¹ *ᵥ y) i) = (h.mat *ᵥ u) ⬝ᵥ ((h.matᵀ)⁻¹ *ᵥ y) := rfl
    rw [e1, e2, dotProduct_comm (h.mat *ᵥ u), dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec,
      mul_nonsing_inv _ hinv, one_mulVec, dotProduct_comm]
  rw [hpair]
  calc ‖∑ i, (h.mat *ᵥ u) i * ((h.matᵀ)⁻¹ *ᵥ y) i‖
      ≤ ∑ i, ‖(h.mat *ᵥ u) i‖ * ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ √(∑ i, ‖(h.mat *ᵥ u) i‖ ^ 2) * √(∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = h.norm u * h.dualNorm y := rfl

/- English proof (translation)
Establish `hinv : IsUnit h.matᵀ.det` using `by rw [det_transpose]; exact h.isUnit_det`. Unfold `HermNorm.dualNorm`. Apply `Real.sqrt_pos.mpr` to reduce the goal to its premises. Establish `hBy : (h.matᵀ)⁻¹ *ᵥ y ≠ 0`. Introduce `h0`.

Apply `hy` to reduce the goal to its premises. Use `congrArg (fun x => h.matᵀ *ᵥ x) h0` as an intermediate fact. Simplify using `only [mulVec_mulVec, mul_nonsing_inv _ hinv, one_mulVec, mulVec_zero] at this`. Conclude with `this`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hBy`.

Conclude with `Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by`. Establish `: 0 < ‖((h.matᵀ)⁻¹ *ᵥ y) i‖` using `norm_pos_iff.mpr hi`. Use the proof step `positivity⟩`.
-/
theorem HermNorm.dualNorm_pos (h : HermNorm n) {y : Fin n → ℂ} (hy : y ≠ 0) : 0 < h.dualNorm y := by
  have hinv : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  unfold HermNorm.dualNorm
  apply Real.sqrt_pos.mpr
  have hBy : (h.matᵀ)⁻¹ *ᵥ y ≠ 0 := by
    intro h0
    apply hy
    have := congrArg (fun x => h.matᵀ *ᵥ x) h0
    simp only [mulVec_mulVec, mul_nonsing_inv _ hinv, one_mulVec, mulVec_zero] at this
    exact this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hBy
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by
    have : 0 < ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ := norm_pos_iff.mpr hi
    positivity⟩

/- English proof (translation)
Establish `hy0 : y ≠ 0` using `by rintro rfl; simp at hy`. Establish `hd` using `h.dualNorm_pos hy0`. Establish `hnum : 0 < ‖∑ j, u j * y j‖` using `norm_pos_iff.mpr hy`. Unfold `fsLog`. Apply `Real.log_le_log (div_pos hnum hd)` to reduce the goal to its premises.

Rewrite using `[div_le_iff₀ hd]`. Conclude with `h.norm_pairing_le u y`.
-/
theorem fsLog_le (h : HermNorm n) {u y : Fin n → ℂ} (hy : ∑ j, u j * y j ≠ 0) :
    fsLog h u y ≤ Real.log (h.norm u) := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hd := h.dualNorm_pos hy0
  have hnum : 0 < ‖∑ j, u j * y j‖ := norm_pos_iff.mpr hy
  unfold fsLog
  apply Real.log_le_log (div_pos hnum hd)
  rw [div_le_iff₀ hd]
  exact h.norm_pairing_le u y

/- English proof (translation)
Establish `hc : Continuous (h.pointOf)`. Unfold `HermNorm.pointOf`. Use `fun_prop`. Establish `hclosed : IsClosed {y : EuclideanSpace ℂ (Fin n) | ∀ q ∈ W, eval (h.pointOf y) q = 0}`. Establish `: {y : EuclideanSpace ℂ (Fin n) | ∀ q ∈ W, eval (h.pointOf y) q = 0} = ⋂ q ∈ W, {y | eval (h.pointOf y) q = 0}`.

Use extensionality with `y`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `isClosed_biInter fun q _ => isClosed_eq ((continuous_eval q).comp hc) continuous_const`. Establish `hopen : MeasurableSet (Metric.ball (0 : EuclideanSpace ℂ (Fin n)) 1)` using `Metric.isOpen_ball.measurableSet`.

Use `hopen.inter hclosed.measurableSet` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`. Simplify using `[coneBall, Metric.mem_ball]`.
-/
theorem measurableSet_coneBall (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) :
    MeasurableSet (coneBall h W) := by
  have hc : Continuous (h.pointOf) := by
    unfold HermNorm.pointOf
    fun_prop
  have hclosed : IsClosed {y : EuclideanSpace ℂ (Fin n) | ∀ q ∈ W, eval (h.pointOf y) q = 0} := by
    have : {y : EuclideanSpace ℂ (Fin n) | ∀ q ∈ W, eval (h.pointOf y) q = 0} =
        ⋂ q ∈ W, {y | eval (h.pointOf y) q = 0} := by
      ext y; simp
    rw [this]
    exact isClosed_biInter fun q _ => isClosed_eq ((continuous_eval q).comp hc) continuous_const
  have hopen : MeasurableSet (Metric.ball (0 : EuclideanSpace ℂ (Fin n)) 1) :=
    Metric.isOpen_ball.measurableSet
  have := hopen.inter hclosed.measurableSet
  convert this using 1
  ext y
  simp [coneBall, Metric.mem_ball]

/- English proof (translation)
Introduce `n e δ h W f u hW hf hδ hu`. Use `set μ := Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (X := EuclideanSpace ℂ (Fin n))`. Use `set c := (μ {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}).toReal`. Establish `hmass` using `hMass n e δ h W f hW hf hδ`. Establish `hfin` using `hFin n e h W f hW hf`.

Establish `hS` using `measurableSet_coneBall h W`. Establish `hconst : IntegrableOn (fun _ : EuclideanSpace ℂ (Fin n) => Real.log (h.norm u)) (coneBall h W) μ` using `integrableOn_const hfin.ne`. Establish `hae : (fun y => fsLog h u (h.pointOf y)) ≤ᵐ[μ.restrict (coneBall h W)] fun _ => Real.log (h.norm u)`. Rewrite using `[Filter.EventuallyLE, ae_restrict_iff' hS]`. Establish `hnull` using `hNull n e h W f u hW hf hu`.

Use `measure_mono_null (fun y hy => ?_) hnull` and prove the remaining obligations. Establish `hy' : ¬(y ∈ coneBall h W → fsLog h u (h.pointOf y) ≤ Real.log (h.norm u))` using `hy`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Conclude with `hy' fun h' => absurd h' hc`.

Use `show ∑ j, u j * h.pointOf y j = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hy' fun _ => fsLog_le h hne`. Establish `hle` using `setIntegral_mono_ae_restrict (hInt n e h W f u hW hf hu) hconst hae`. Rewrite `hle` using `[setIntegral_const, smul_eq_mul]`.

Unfold `coneIntegral at hmass ⊢`. Express the relevant statement in the definitionally equal form `(∫ y in coneBall h W, fsLog h u (h.pointOf y) ∂μ) / c ≤ δ * Real.log (h.norm u)`. Express the relevant statement in the definitionally equal form `(∫ y in coneBall h W, (1 : ℝ) ∂μ) / c = δ at hmass`. Rewrite `hmass` using `[setIntegral_const, smul_eq_mul, mul_one]`. Break down `(le_or_gt c 0) with hc | hc` into its components or cases.

Establish `hc0 : c = 0` using `le_antisymm hc ENNReal.toReal_nonneg`. Rewrite `hmass`, the goal using `[hc0, div_zero]`. Rewrite using `[← hmass]`. Simplify using the standard rewrite rules. Rewrite using `[div_le_iff₀ hc]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hmass]`. Clear the denominators using the available nonvanishing facts.
-/
theorem ConeLogBound.proof (hMass : ConeIntegralMass.Statement) (hFin : ConeBallFinite.Statement)
    (hInt : ConeFsLogIntegrable.Statement) (hNull : ConeHyperplaneNull.Statement) :
    ConeLogBound.Statement := by
  intro n e δ h W f u hW hf hδ hu
  set μ := Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (X := EuclideanSpace ℂ (Fin n))
  set c := (μ {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}).toReal
  have hmass := hMass n e δ h W f hW hf hδ
  have hfin := hFin n e h W f hW hf
  have hS := measurableSet_coneBall h W
  have hconst : IntegrableOn (fun _ : EuclideanSpace ℂ (Fin n) => Real.log (h.norm u)) (coneBall h W) μ :=
    integrableOn_const hfin.ne
  have hae : (fun y => fsLog h u (h.pointOf y)) ≤ᵐ[μ.restrict (coneBall h W)]
      fun _ => Real.log (h.norm u) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' hS]
    have hnull := hNull n e h W f u hW hf hu
    refine measure_mono_null (fun y hy => ?_) hnull
    have hy' : ¬(y ∈ coneBall h W → fsLog h u (h.pointOf y) ≤ Real.log (h.norm u)) := hy
    refine ⟨?_, ?_⟩
    · by_contra hc
      exact hy' fun h' => absurd h' hc
    · show ∑ j, u j * h.pointOf y j = 0
      by_contra hne
      exact hy' fun _ => fsLog_le h hne
  have hle := setIntegral_mono_ae_restrict (hInt n e h W f u hW hf hu) hconst hae
  rw [setIntegral_const, smul_eq_mul] at hle
  unfold coneIntegral at hmass ⊢
  change (∫ y in coneBall h W, fsLog h u (h.pointOf y) ∂μ) / c ≤ δ * Real.log (h.norm u)
  change (∫ y in coneBall h W, (1 : ℝ) ∂μ) / c = δ at hmass
  rw [setIntegral_const, smul_eq_mul, mul_one] at hmass
  rcases (le_or_gt c 0) with hc | hc
  · have hc0 : c = 0 := le_antisymm hc ENNReal.toReal_nonneg
    rw [hc0, div_zero] at hmass ⊢
    rw [← hmass]
    simp
  · rw [div_le_iff₀ hc]
    calc _ ≤ μ.real (coneBall h W) * Real.log (h.norm u) := hle
      _ = δ * Real.log (h.norm u) * c := by
        rw [← hmass]
        field_simp

end

end GroundTheory.Heights₂.Heights
