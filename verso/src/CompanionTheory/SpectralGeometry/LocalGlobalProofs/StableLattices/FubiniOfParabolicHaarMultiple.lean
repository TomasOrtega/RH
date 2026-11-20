import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.Fub2

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.RgFubOf

open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fubini_of_parabolic_multiple : CompanionTheory.RgExh.Dec.N.S.Fub2 → CompanionTheory.RgExh.Dec.N.S.Fub := by
  intro h n ε A hA
  obtain ⟨μN, μM, hN, hM, h0, hinv, hκ, hH⟩ := h n ε A hA
  refine ⟨μN, μM, hN, hM, h0, hinv, hκ, ?_⟩
  rintro μ ⟨ν, rfl, hν⟩ E hE hnull
  haveI := hN
  haveI := hM
  obtain ⟨c, -, -, hc⟩ := hH ν hν
  have hF := hc (E.indicator 1) (measurable_one.indicator hE)
  have hI : muPar ε A ν E = ∫⁻ x, E.indicator 1 x ∂(muPar ε A ν) := (lintegral_indicator_one hE).symm
  refine hI.trans (hF.trans ?_)
  have hae : ∀ᵐ p ∂(μN.prod μM), p.1 * p.2 ∉ E := measure_eq_zero_iff_ae_notMem.1 hnull
  have hae2 := Measure.ae_ae_of_ae_prod hae
  have hz : (∫⁻ u, ∫⁻ m, modA A m * E.indicator 1 (u * m) ∂μM ∂μN) = 0 := by
    have : (fun u => ∫⁻ m, modA A m * E.indicator 1 (u * m) ∂μM) =ᵐ[μN] fun _ => 0 := by
      filter_upwards [hae2] with u hu
      have : (fun m : Formalism.REAL.UJ ε => modA A m * E.indicator 1 (u * m)) =ᵐ[μM] fun _ => 0 := by
        filter_upwards [hu] with m hm
        simp [Set.indicator_of_notMem hm]
      rw [lintegral_congr_ae this]
      simp
    rw [lintegral_congr_ae this]
    simp
  rw [hz, mul_zero]

end GlobalTheory.CompanionTheory.RgFubOf
