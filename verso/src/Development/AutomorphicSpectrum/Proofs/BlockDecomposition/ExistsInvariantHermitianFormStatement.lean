import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantHermitianForm
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
Apply `GlobalTheory.CompanionTheory.ClozelHerm.exists_isHerm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsInvariantHermitianForm.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.exists_invariant_hermitian_form : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ, IsHerm π B := by
  first | exact @GlobalTheory.CompanionTheory.ClozelHerm.exists_isHerm | exact GlobalTheory.CompanionTheory.ClozelHerm.exists_isHerm | (intros; apply GlobalTheory.CompanionTheory.ClozelHerm.exists_isHerm <;> assumption)
