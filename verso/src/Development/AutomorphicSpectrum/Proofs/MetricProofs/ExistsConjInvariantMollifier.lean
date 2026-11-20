import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsConjInvariantMollifier

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `n`. Take `⟨ρ⟩` from `ReciprocityTheory.AnForm.A.mollifierInhabit_thm n`. Establish `hmp : MeasureTheory.MeasurePreserving (fun v : Fin n → ℂ => star v)` using `MeasureTheory.volume_preserving_pi (fun _ => Complex.conjLIE.measurePreserving)`. Establish `hme : MeasurableEmbedding (fun v : Fin n → ℂ => star v)` using `(starLinearEquiv ℝ (A := Fin n → ℂ)).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding`. Establish `hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun v : Fin n → ℂ => star v)` using `contDiff_pi.2 fun i => Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ i)`.

Establish `hI : MeasureTheory.Integrable ρ.toFun` using `MeasureTheory.Integrable.of_integral_ne_zero (by rw [ρ.integral_eq_one]; norm_num)`. Establish `hcomp : ∫ w : Fin n → ℂ, ρ.toFun (star w) = 1`. Rewrite using `[hmp.integral_comp hme ρ.toFun, ρ.integral_eq_one]`. Establish `hI2 : MeasureTheory.Integrable (fun w : Fin n → ℂ => ρ.toFun (star w))` using `MeasureTheory.Integrable.of_integral_ne_zero (by rw [hcomp]; norm_num)`. Use `⟨⟨fun v => (ρ.toFun v + ρ.toFun (star v)) / 2, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `(ρ.contDiff.add (ρ.contDiff.comp hsm)).div_const 2`. Introduce `w`. Conclude with `div_nonneg (add_nonneg (ρ.nonneg _) (ρ.nonneg _)) two_pos.le`. Introduce `w hw`. Assume the negation of the conclusion as `h`.

Establish `h1 : ρ.toFun w = 0`. Assume the negation of the conclusion as `h'`. Conclude with `h (ρ.support_subset h')`. Establish `h2 : ρ.toFun (star w) = 0`. Assume the negation of the conclusion as `h'`.

Establish `hb` using `ρ.support_subset h'`. Rewrite `hb` using `[Metric.mem_ball, dist_zero_right, norm_star]`. Conclude with `h (by rw [Metric.mem_ball, dist_zero_right]; exact hb)`. Conclude with `hw (by simp [h1, h2])`. Use `show ∫ w : Fin n → ℂ, (ρ.toFun w + ρ.toFun (star w)) / 2 = 1`.

Rewrite using `[MeasureTheory.integral_div, MeasureTheory.integral_add hI hI2, ρ.integral_eq_one, hcomp]`. Evaluate the numerical expressions. Introduce `c w hc show (ρ.toFun (c • w) + ρ.toFun (star (c • w))) / 2 = (ρ.toFun w + ρ.toFun (star w)) / 2`. Rewrite using `[star_smul, ρ.circle_inv c w hc, ρ.circle_inv (star c) (star w) (by rw [norm_star]; exact hc)]`. Introduce `v show (ρ.toFun (star v) + ρ.toFun (star (star v))) / 2 = (ρ.toFun v + ρ.toFun (star v)) / 2`.

Rewrite using `[star_star, add_comm]`.
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_conj_invariant_mollifier : ∀ n : ℕ, ∃ ρ : ReciprocityTheory.AnForm.A.Mollifier n, ∀ v, ρ.toFun (star v) = ρ.toFun v := by
  intro n
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm n
  have hmp : MeasureTheory.MeasurePreserving (fun v : Fin n → ℂ => star v) :=
    MeasureTheory.volume_preserving_pi (fun _ => Complex.conjLIE.measurePreserving)
  have hme : MeasurableEmbedding (fun v : Fin n → ℂ => star v) :=
    (starLinearEquiv ℝ (A := Fin n → ℂ)).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun v : Fin n → ℂ => star v) :=
    contDiff_pi.2 fun i => Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ i)
  have hI : MeasureTheory.Integrable ρ.toFun :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [ρ.integral_eq_one]; norm_num)
  have hcomp : ∫ w : Fin n → ℂ, ρ.toFun (star w) = 1 := by
    rw [hmp.integral_comp hme ρ.toFun, ρ.integral_eq_one]
  have hI2 : MeasureTheory.Integrable (fun w : Fin n → ℂ => ρ.toFun (star w)) :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [hcomp]; norm_num)
  refine ⟨⟨fun v => (ρ.toFun v + ρ.toFun (star v)) / 2, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (ρ.contDiff.add (ρ.contDiff.comp hsm)).div_const 2
  · intro w
    exact div_nonneg (add_nonneg (ρ.nonneg _) (ρ.nonneg _)) two_pos.le
  · intro w hw
    by_contra h
    have h1 : ρ.toFun w = 0 := by
      by_contra h'
      exact h (ρ.support_subset h')
    have h2 : ρ.toFun (star w) = 0 := by
      by_contra h'
      have hb := ρ.support_subset h'
      rw [Metric.mem_ball, dist_zero_right, norm_star] at hb
      exact h (by rw [Metric.mem_ball, dist_zero_right]; exact hb)
    exact hw (by simp [h1, h2])
  · show ∫ w : Fin n → ℂ, (ρ.toFun w + ρ.toFun (star w)) / 2 = 1
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add hI hI2, ρ.integral_eq_one, hcomp]
    norm_num
  · intro c w hc
    show (ρ.toFun (c • w) + ρ.toFun (star (c • w))) / 2 = (ρ.toFun w + ρ.toFun (star w)) / 2
    rw [star_smul, ρ.circle_inv c w hc, ρ.circle_inv (star c) (star w) (by rw [norm_star]; exact hc)]
  · intro v
    show (ρ.toFun (star v) + ρ.toFun (star (star v))) / 2 = (ρ.toFun v + ρ.toFun (star v)) / 2
    rw [star_star, add_comm]
