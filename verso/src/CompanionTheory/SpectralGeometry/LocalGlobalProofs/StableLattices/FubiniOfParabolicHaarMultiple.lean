import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.Fub2

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.RgFubOf

open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S

/- English proof (translation)
Introduce `h n ε A hA`. Take `⟨μN, μM, hN, hM, h0, hinv, hκ, hH⟩` from `h n ε A hA`. Use `⟨μN, μM, hN, hM, h0, hinv, hκ, ?_⟩` and prove the remaining obligations. Introduce and unpack `μ ⟨ν, rfl, hν⟩ E hE hnull`. Use `haveI := hN`.

Use `haveI := hM`. Take `⟨c, -, -, hc⟩` from `hH ν hν`. Establish `hF` using `hc (E.indicator 1) (measurable_one.indicator hE)`. Establish `hI : muPar ε A ν E = ∫⁻ x, E.indicator 1 x ∂(muPar ε A ν)` using `(lintegral_indicator_one hE).symm`. Use `hI.trans (hF.trans ?_)` and prove the remaining obligations.

Establish `hae : ∀ᵐ p ∂(μN.prod μM), p.1 * p.2 ∉ E` using `measure_eq_zero_iff_ae_notMem.1 hnull`. Establish `hae2` using `Measure.ae_ae_of_ae_prod hae`. Establish `hz : (∫⁻ u, ∫⁻ m, modA A m * E.indicator 1 (u * m) ∂μM ∂μN) = 0`. Establish `: (fun u => ∫⁻ m, modA A m * E.indicator 1 (u * m) ∂μM) =ᵐ[μN] fun _ => 0` using `by filter_upwards [hae2] with u hu`. Establish `: (fun m : Formalism.REAL.UJ ε => modA A m * E.indicator 1 (u * m)) =ᵐ[μM] fun _ => 0` using `by filter_upwards [hu] with m hm`.

Simplify using `[Set.indicator_of_notMem hm]`. Rewrite using `[lintegral_congr_ae this]`. Simplify using the standard rewrite rules. Rewrite using `[lintegral_congr_ae this]`. Simplify using the standard rewrite rules.

Rewrite using `[hz, mul_zero]`.
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
