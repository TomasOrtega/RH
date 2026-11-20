import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralEigenExponential
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
Apply `GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCentralEigenExponential.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.central_eigen_exponential : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (c : ℂ), lie E a (oneL E a) φ = c • φ → ∀ (t : ℝ) (g : GA E a), φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = Complex.exp (c * t) * φ.1 g := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre | exact GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre | (intros; apply GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre <;> assumption)
