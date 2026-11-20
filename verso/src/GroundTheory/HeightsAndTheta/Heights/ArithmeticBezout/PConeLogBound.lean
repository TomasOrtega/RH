import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField Matrix

noncomputable section

variable {n : ℕ}

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact.

A detailed English derivation is pending.
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
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Replace the relevant objects with their definitions. Express the relevant assertion in an equivalent form by its definition. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. A detailed English derivation is pending.
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
