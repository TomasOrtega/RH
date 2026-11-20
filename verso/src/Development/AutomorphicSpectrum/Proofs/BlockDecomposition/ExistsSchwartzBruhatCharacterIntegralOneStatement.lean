import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSchwartzBruhatCharacterIntegralOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FrobNz.exists_SB_integral_mul_char_eq_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsSchwartzBruhatCharacterIntegralOne.lean&line=110#L110)
-/
theorem _root_.GlobalTheory.T.exists_schwartzBruhat_character_integral_one : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (χ : G →* ℂˣ), Continuous (fun g => (χ g : ℂ)) → ∃ α : SB G, ∫ x, (α : G → ℂ) x * (χ x : ℂ) ∂μ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.FrobNz.exists_SB_integral_mul_char_eq_one | exact GlobalTheory.CompanionTheory.FrobNz.exists_SB_integral_mul_char_eq_one | (intros; apply GlobalTheory.CompanionTheory.FrobNz.exists_SB_integral_mul_char_eq_one <;> assumption)
