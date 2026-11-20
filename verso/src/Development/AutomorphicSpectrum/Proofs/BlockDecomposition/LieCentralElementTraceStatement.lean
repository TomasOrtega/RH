import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieCentralElementTrace
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLieCentralElementTrace.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.lie_central_element_trace : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), lie E a (oneL E a) = ∑ τ : E →+* ℂ, ∑ i : Fin a, Eop τ i i := by
  first | exact @GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop | exact GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop | (intros; apply GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop <;> assumption)
