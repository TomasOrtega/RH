import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxA3

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ D`. Establish `hnull : (volume : Measure ((Fin r → ℂ) × ℂ)) (Set.univ ×ˢ {w : ℂ | Complex.normSq w = Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z'}) = 0`. Rewrite using `[Measure.volume_eq_prod, Measure.prod_prod]`. Establish `h0 : (volume : Measure ℂ) {w : ℂ | Complex.normSq w = Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z'} = 0`. Apply `measure_mono_null (t := Metric.sphere (0 : ℂ) (Real.sqrt (Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z')))` to reduce the goal to its premises.

Introduce `w hw`. Simplify using `only [Set.mem_setOf_eq] at hw`. Simplify using `only [Metric.mem_sphere, dist_zero_right]`. Rewrite using `[← hw, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]`. Conclude with `Measure.addHaar_sphere _ _ _`.

Rewrite using `[h0, mul_zero]`. Rewrite using `[ae_restrict_iff' (Formalism.FourierDecayAlt.P.B7.measurableSet_Qset D)]`. Use `filter_upwards [compl_mem_ae_iff.mpr hnull] with q hq hqQ`. Apply `Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D` to reduce the goal to its premises. Simplify using `only [B.Qset, Set.mem_setOf_eq] at hqQ`.

Unfold `Formalism.QuantumDeterminants.bcWeight at hqQ`. Use `split_ifs at hqQ with hle`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Establish `hp : (∏ b : Fin r, ‖q.1 b‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r b - 2))) = 0`.

Apply `Finset.prod_eq_zero (Finset.mem_univ a)` to reduce the goal to its premises. Rewrite using `[ha, norm_zero]`. Apply `zero_pow` to reduce the goal to its premises. Use `a.isLt` as an intermediate fact. Unfold `Formalism.QuantumDeterminants.Mdim`.

Use linear arithmetic over natural numbers and integers. Rewrite `hqQ` using `[hp, zero_mul]`. Conclude with `lt_irrefl _ hqQ`. Use `lt_of_le_of_ne hle ?_` and prove the remaining obligations. Introduce `heq`.

Conclude with `hq ⟨Set.mem_univ _, heq.symm⟩`. Conclude with `absurd hqQ (lt_irrefl _)`.
-/
theorem _root_.Formalism.FourierDecayAlt.P.big_cell_orbit_set : GqOm := by
  intro k r Wp Wq _ _ _ _ D
  have hnull : (volume : Measure ((Fin r → ℂ) × ℂ))
      (Set.univ ×ˢ {w : ℂ | Complex.normSq w = Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z'}) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    have h0 : (volume : Measure ℂ)
        {w : ℂ | Complex.normSq w = Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z'} = 0 := by
      apply measure_mono_null (t := Metric.sphere (0 : ℂ)
        (Real.sqrt (Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z')))
      · intro w hw
        simp only [Set.mem_setOf_eq] at hw
        simp only [Metric.mem_sphere, dist_zero_right]
        rw [← hw, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
      · exact Measure.addHaar_sphere _ _ _
    rw [h0, mul_zero]
  rw [ae_restrict_iff' (Formalism.FourierDecayAlt.P.B7.measurableSet_Qset D)]
  filter_upwards [compl_mem_ae_iff.mpr hnull] with q hq hqQ
  apply Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D
  simp only [B.Qset, Set.mem_setOf_eq] at hqQ
  unfold Formalism.QuantumDeterminants.bcWeight at hqQ
  split_ifs at hqQ with hle
  · refine ⟨?_, ?_⟩
    · intro a ha
      have hp : (∏ b : Fin r, ‖q.1 b‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r b - 2))) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ a)
        rw [ha, norm_zero]
        apply zero_pow
        have := a.isLt
        unfold Formalism.QuantumDeterminants.Mdim
        omega
      rw [hp, zero_mul] at hqQ
      exact lt_irrefl _ hqQ
    · refine lt_of_le_of_ne hle ?_
      intro heq
      exact hq ⟨Set.mem_univ _, heq.symm⟩
  · exact absurd hqQ (lt_irrefl _)

end Formalism.FourierDecayAlt.P.JFxA3
