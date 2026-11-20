import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeLocalMass
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeJacMeasurable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeTangentDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsTangentGaussInvariant
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

/- English proof (translation)
Introduce `q hq`. Establish `hd : ∀ d, eval (h.pointOf y) (∑ j, X j * pderiv j (homogeneousComponent d q)) = 0`. Introduce `d`. Rewrite using `[(homogeneousComponent_isHomogeneous d q).sum_X_mul_pderiv, map_nsmul, hy _ (hJ.isHomog q hq d), smul_zero]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [map_sum, Finset.mul_sum]`. Conclude with `Finset.sum_comm`. Use `_ = 0 := Finset.sum_eq_zero fun d _ => hd d`.
-/
theorem mem_coneTangent_self {n : ℕ} (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hJ : IsProjPrime J) {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ coneSet h J) :
    y ∈ coneTangent h J y := by
  intro q hq
  have hd : ∀ d, eval (h.pointOf y) (∑ j, X j * pderiv j (homogeneousComponent d q)) = 0 := by
    intro d
    rw [(homogeneousComponent_isHomogeneous d q).sum_X_mul_pderiv, map_nsmul,
      hy _ (hJ.isHomog q hq d), smul_zero]
  calc ∑ j, eval (h.pointOf y) (pderiv j q) * h.pointOf y j
      = eval (h.pointOf y) (∑ j, X j * pderiv j q) := by simp [map_sum, mul_comm]
    _ = ∑ d ∈ Finset.range (q.totalDegree + 1),
          eval (h.pointOf y) (∑ j, X j * pderiv j (homogeneousComponent d q)) := by
        conv_lhs => rw [← sum_homogeneousComponent q]
        simp only [map_sum, Finset.mul_sum]
        exact Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun d _ => hd d

/- English proof (translation)
Establish `: coneSet h J = ⋂ q ∈ J, {y | eval (h.pointOf y) q = 0}`. Use extensionality with `y`. Simplify using `[coneSet]`. Rewrite using `[this]`. Conclude with `isClosed_biInter fun q _ => isClosed_eq ((MvPolynomial.continuous_eval q).comp h.continuous_pointOf) continuous_const`.
-/
theorem isClosed_coneSet {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsClosed (coneSet h J) := by
  have : coneSet h J = ⋂ q ∈ J, {y | eval (h.pointOf y) q = 0} := by
    ext y
    simp [coneSet]
  rw [this]
  exact isClosed_biInter fun q _ =>
    isClosed_eq ((MvPolynomial.continuous_eval q).comp h.continuous_pointOf) continuous_const

/- English proof (translation)
Establish `: IsLocallyFiniteMeasure (μ.restrict C)` using `⟨fun x => ⟨Metric.ball 0 (‖x‖ + 1), Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (by linarith)), by`. Rewrite using `[Measure.restrict_apply Metric.isOpen_ball.measurableSet, Set.inter_comm]`. Conclude with `hC _⟩⟩`. Use `infer_instance`.
-/
theorem sFinite_restrict_of_ball {n : ℕ} (μ : Measure (EuclideanSpace ℂ (Fin n)))
    (C : Set (EuclideanSpace ℂ (Fin n))) (hC : ∀ R : ℝ, μ (C ∩ Metric.ball 0 R) < ⊤) :
    SFinite (μ.restrict C) := by
  have : IsLocallyFiniteMeasure (μ.restrict C) := ⟨fun x => ⟨Metric.ball 0 (‖x‖ + 1),
    Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (by linarith)), by
      rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet, Set.inter_comm]
      exact hC _⟩⟩
  infer_instance

/- English proof (translation)
Introduce `n m h J hJ hm hmn hfib`. Establish `: SFinite ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) : Measure (EuclideanSpace ℂ (Fin n))).restrict (coneSet h J))` using `sFinite_restrict_of_ball _ _ (hMass n m h J hJ hm hmn hfib)`. Establish `hG : Measurable fun π : Fin m → Fin n → ℂ => matGauss π`. Unfold `matGauss`. Conclude with `(by fun_prop : Continuous fun π : Fin m → Fin n → ℂ => Real.exp (-∑ i, ∑ j, ‖π i j‖ ^ 2)).measurable.ennreal_ofReal`.

Establish `hP : Continuous fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => linProj p.1 p.2`. Unfold `linProj`. Use `fun_prop`. Establish `hF : AEMeasurable (Function.uncurry fun (π : Fin m → Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) => matGauss π * ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) * ENNReal.ofReal (coneJac h J π y))) ((volume : Measure (Fin m → Fin n → ℂ)).prod ((Measure.hau …` using `(hG.comp measurable_fst).aemeasurable.mul (((measurable_one.indicator Metric.isOpen_ball.measurableSet).comp hP.measurable).aemeasurable.mul (hMeas n m h J hJ hm hmn hfib).ennreal_ofReal)`. Rewrite using `[show (fun π : Fin m → Fin n → ℂ => matGauss π * ∫⁻ y in coneSet h J, (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) * ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ))) = fun π => ∫⁻ y in coneSet h J, matGauss π * ((Metric.b …`.

Use function extensionality and compare the values at `fun π => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm,`. Use `lintegral_lintegral_swap hF]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hDim n m h J hJ hm hmn hfib, ae_restrict_mem (isClosed_coneSet h J).measurableSet] with y hy hyC`. Simplify using `only [← mul_assoc]`.

Conclude with `hInv n m hm hmn _ hy y (mem_coneTangent_self h hJ hyC)`.
-/
theorem ConeTangentAverage.proof (hMass : ConeLocalMass.Statement)
    (hMeas : ConeJacMeasurable.Statement) (hDim : ConeTangentDim.Statement)
    (hInv : TangentGaussInvariant.Statement) : ConeTangentAverage.Statement := by
  intro n m h J hJ hm hmn hfib
  have : SFinite ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) :
      Measure (EuclideanSpace ℂ (Fin n))).restrict (coneSet h J)) :=
    sFinite_restrict_of_ball _ _ (hMass n m h J hJ hm hmn hfib)
  have hG : Measurable fun π : Fin m → Fin n → ℂ => matGauss π := by
    unfold matGauss
    exact (by fun_prop : Continuous fun π : Fin m → Fin n → ℂ =>
      Real.exp (-∑ i, ∑ j, ‖π i j‖ ^ 2)).measurable.ennreal_ofReal
  have hP : Continuous fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => linProj p.1 p.2 := by
    unfold linProj
    fun_prop
  have hF : AEMeasurable (Function.uncurry fun (π : Fin m → Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) =>
      matGauss π * ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
        ENNReal.ofReal (coneJac h J π y)))
      ((volume : Measure (Fin m → Fin n → ℂ)).prod
        ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J))) :=
    (hG.comp measurable_fst).aemeasurable.mul
      (((measurable_one.indicator Metric.isOpen_ball.measurableSet).comp hP.measurable).aemeasurable.mul
        (hMeas n m h J hJ hm hmn hfib).ennreal_ofReal)
  rw [show (fun π : Fin m → Fin n → ℂ => matGauss π *
      ∫⁻ y in coneSet h J, (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
        ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ))) =
      fun π => ∫⁻ y in coneSet h J, matGauss π *
        ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
          ENNReal.ofReal (coneJac h J π y)) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) from
    funext fun π => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm,
    lintegral_lintegral_swap hF]
  refine lintegral_congr_ae ?_
  filter_upwards [hDim n m h J hJ hm hmn hfib, ae_restrict_mem (isClosed_coneSet h J).measurableSet]
    with y hy hyC
  simp only [← mul_assoc]
  exact hInv n m hm hmn _ hy y (mem_coneTangent_self h hJ hyC)

end

end GroundTheory.Heights₂.Heights
