import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GraphChartEventuallyEqSheet
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsSheetMeasurable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter

noncomputable section

variable {n d : ℕ}

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem lift_eval_comp_projHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {x : Fin n → ℂ} (hx : x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J) :
    (Ideal.Quotient.lift J (MvPolynomial.eval x) fun q hq => hx q hq).comp
        (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom =
      MvPolynomial.eval (A.mulVec x) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [GroundTheory.Heights₂.Heights.ComplexSets.projHom, GroundTheory.Heights₂.Heights.ComplexSets.pullback]
  · intro i
    simp [GroundTheory.Heights₂.Heights.ComplexSets.projHom, GroundTheory.Heights₂.Heights.ComplexSets.pullback,
      GroundTheory.Heights₂.Heights.ComplexSets.linPoly, Matrix.mulVec, dotProduct]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem fibre_finite {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A) (y : Fin d → ℂ) :
    (GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y).Finite := by
  classical
  have hint : ∀ j : Fin n, (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom.IsIntegralElem
      (Ideal.Quotient.mk J (X j)) := fun j => hA.finite.to_isIntegral _
  choose p hpm hp using hint
  refine (Set.Finite.pi (t := fun j => {z : ℂ | ((p j).map (MvPolynomial.eval y)).IsRoot z})
    fun j => Polynomial.finite_setOfPred_isRoot ((hpm j).map _).ne_zero).subset ?_
  rintro x ⟨hx, hxy⟩ j -
  have h := congrArg (Ideal.Quotient.lift J (MvPolynomial.eval x) fun q hq => hx q hq) (hp j)
  rw [Polynomial.hom_eval₂, lift_eval_comp_projHom J A hx, hxy, map_zero] at h
  simpa [Polynomial.IsRoot, Polynomial.eval_map] using h

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem chartAbsDens_indicator_le {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (l : (Fin n → ℂ) → ℝ) {B C : Set (Fin n → ℂ)} (hBC : B ⊆ C)
    (y : Fin d → ℂ) :
    0 ≤ GroundTheory.Heights₂.Heights.chartAbsDens J A (B.indicator l) φ y ∧
      GroundTheory.Heights₂.Heights.chartAbsDens J A (B.indicator l) φ y ≤
        GroundTheory.Heights₂.Heights.chartAbsDens J A (C.indicator l) φ y := by
  unfold GroundTheory.Heights₂.Heights.chartAbsDens GroundTheory.Heights₂.Heights.sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (fibre_finite hA y),
    finsum_mem_eq_finite_toFinset_sum _ (fibre_finite hA y)]
  refine ⟨Finset.sum_nonneg fun x _ => ?_, Finset.sum_le_sum fun x _ => ?_⟩
  · split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  · split_ifs
    · dsimp only
      rw [abs_mul, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      by_cases hx : x ∈ B
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hBC hx)]
      · rw [Set.indicator_of_notMem hx, abs_zero]
        exact abs_nonneg _
    · exact le_rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem LogIntegrableOn.to_current (h : LogIntegrableOn.Statement) :
    GroundTheory.Heights₂.Heights.LogIntegrable.Statement := by
  intro n d J A u φ R hJ hdim hA hu hφ
  have hJ' : IsAffVariety J d := ⟨hJ, hdim⟩
  exact (projIntegrable_iff _ _ _ _).mp
    (h n d J A φ u (Metric.closedBall 0 R) hJ' ((isFiniteProj_iff hJ').mpr hA) hφ hu
      measurableSet_closedBall Metric.isBounded_closedBall)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem LogIntegrable.logIntegrableOn_of_logIntegrable (hM : GroundTheory.Heights₂.Heights.SheetSumMeasurable.Statement)
    (h : GroundTheory.Heights₂.Heights.LogIntegrable.Statement) : LogIntegrableOn.Statement := by
  intro n d J A φ u B hJ hA hφ hu hB hBb
  have hA' := (isFiniteProj_iff hJ).mp hA
  obtain ⟨R, hR⟩ := hBb.subset_closedBall 0
  have hI := h n d J A u φ R hJ.isPrime hJ.dim hA' hu hφ
  have hcont : Continuous fun x : Fin n → ℂ => GroundTheory.Heights₂.Heights.linEval u x := by
    unfold GroundTheory.Heights₂.Heights.linEval
    fun_prop
  have hmeas : Measurable (B.indicator fun x => Real.log ‖GroundTheory.Heights₂.Heights.linEval u x‖) :=
    (Real.measurable_log.comp (continuous_norm.comp hcont).measurable).indicator hB
  rw [projIntegrable_iff]
  refine hI.mono' (hM n d J A _ φ hJ.isPrime hJ.dim hA' hmeas hφ).2.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  obtain ⟨h0, h1⟩ := chartAbsDens_indicator_le hA' φ
    (fun x => Real.log ‖GroundTheory.Heights₂.Heights.linEval u x‖) hR y
  rw [Real.norm_eq_abs]
  exact (abs_of_nonneg h0).le.trans h1

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem LogIntegrable.equiv (hM : GroundTheory.Heights₂.Heights.SheetSumMeasurable.Statement) :
    GroundTheory.Heights₂.Heights.LogIntegrable.Statement ↔ LogIntegrableOn.Statement :=
  ⟨LogIntegrable.logIntegrableOn_of_logIntegrable hM, LogIntegrableOn.to_current⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
