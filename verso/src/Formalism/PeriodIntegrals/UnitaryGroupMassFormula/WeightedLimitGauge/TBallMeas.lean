import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

/- English proof (translation)
Use `set n := 2 * r + k + 1`. Establish `hexp : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp A)`. Set `_ : NormedRing (Matrix (Fin n) (Fin n) ℂ)` to `Matrix.linftyOpNormedRing`. Establish `: @CompleteSpace (Matrix (Fin n) (Fin n) ℂ) PseudoMetricSpace.toUniformSpace`. Set `_ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ)` to `Matrix.linftyOpNormedAlgebra`.

Conclude with `FiniteDimensional.complete ℂ _`. Set `_ : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ)` to `Matrix.linftyOpNormedAlgebra (R := ℚ)`. Conclude with `NormedSpace.exp_continuous`. Establish `hun : Continuous (fun x : EuclideanSpace ℝ (Fin n × Fin n × Bool) => unrealify x)`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations.

Establish `hmk : Continuous (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))` using `Complex.equivRealProdCLM.symm.continuous`. Use `show Continuous (fun x : EuclideanSpace ℝ (Fin n × Fin n × Bool) => (⟨x (i, j, false), x (i, j, true)⟩ : ℂ))`. Conclude with `hmk.comp ((PiLp.continuous_apply 2 (fun _ : Fin n × Fin n × Bool => ℝ) (i, j, false)).prodMk (PiLp.continuous_apply 2 (fun _ : Fin n × Fin n × Bool => ℝ) (i, j, true)))`. Establish `hall : Continuous (fun x : lieE S => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))))` using `(hexp.comp hun).comp continuous_subtype_val`. Conclude with `continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp hall)`.
-/
theorem continuous_expChart (k r : ℕ) (S : Set (Mat k r)) :
    Continuous (fun x : lieE S =>
      fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) i j :
        lieE S → Mt k r) := by
  set n := 2 * r + k + 1
  have hexp : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp A) := by
    let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    have : @CompleteSpace (Matrix (Fin n) (Fin n) ℂ) PseudoMetricSpace.toUniformSpace := by
      let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
      exact FiniteDimensional.complete ℂ _
    let _ : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra (R := ℚ)
    exact NormedSpace.exp_continuous
  have hun : Continuous (fun x : EuclideanSpace ℝ (Fin n × Fin n × Bool) => unrealify x) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have hmk : Continuous (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) := Complex.equivRealProdCLM.symm.continuous
    show Continuous (fun x : EuclideanSpace ℝ (Fin n × Fin n × Bool) => (⟨x (i, j, false), x (i, j, true)⟩ : ℂ))
    exact hmk.comp ((PiLp.continuous_apply 2 (fun _ : Fin n × Fin n × Bool => ℝ) (i, j, false)).prodMk
      (PiLp.continuous_apply 2 (fun _ : Fin n × Fin n × Bool => ℝ) (i, j, true)))
  have hall : Continuous (fun x : lieE S =>
      NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)))) :=
    (hexp.comp hun).comp continuous_subtype_val
  exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp hall)

/- English proof (translation)
Establish `hball : IsSigmaCompact (Metric.ball (0 : lieE S) ρ)` using `isSigmaCompact_iff_sigmaCompactSpace.2 (haveI : LocallyCompactSpace (Metric.ball (0 : lieE S) ρ) := Metric.isOpen_ball.locallyCompactSpace inferInstance)`. Take `⟨K, hK, hKU⟩` from `hball.image (continuous_expChart k r S)`. Unfold `expBall`. Rewrite using `[← hKU]`. Conclude with `MeasurableSet.iUnion fun n => (hK n).measurableSet`.
-/
theorem measurableSet_expBall (k r : ℕ) (S : Set (Mat k r)) (ρ : ℝ) :
    MeasurableSet (expBall (k := k) (r := r) S ρ) := by
  have hball : IsSigmaCompact (Metric.ball (0 : lieE S) ρ) :=
    isSigmaCompact_iff_sigmaCompactSpace.2
      (haveI : LocallyCompactSpace (Metric.ball (0 : lieE S) ρ) := Metric.isOpen_ball.locallyCompactSpace
       inferInstance)
  obtain ⟨K, hK, hKU⟩ := hball.image (continuous_expChart k r S)
  unfold expBall
  rw [← hKU]
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

/- English proof (translation)
Introduce `k r m ρ`. Establish `hc : Continuous (fun x : Mt k r => fun i j => (m⁻¹ * Matrix.of x) i j)`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`. Use `fun_prop`.

Conclude with `(measurableSet_expBall (k := k) (r := r) (UWb k r) ρ).preimage hc.measurable`.
-/
theorem tBallMeas : TBallMeas := by
  intro k r m ρ
  have hc : Continuous (fun x : Mt k r => fun i j => (m⁻¹ * Matrix.of x) i j) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  exact (measurableSet_expBall (k := k) (r := r) (UWb k r) ρ).preimage hc.measurable

end PI.RhsWLim.W
