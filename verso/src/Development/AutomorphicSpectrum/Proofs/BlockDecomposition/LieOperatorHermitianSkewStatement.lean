import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorHermitianSkew
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
Apply `GlobalTheory.CompanionTheory.ClozelHerm.EopV_adjoint` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLieOperatorHermitianSkew.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.lie_operator_hermitian_skew : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ), IsHerm π B → ∀ (τ : E →+* ℂ) (i j : Fin a) (φ ψ : π.V), B (EopV π τ i j φ) ψ = -B φ (EopV π (NumberField.ComplexEmbedding.conjugate τ) i j ψ) := by
  first | exact @GlobalTheory.CompanionTheory.ClozelHerm.EopV_adjoint | exact GlobalTheory.CompanionTheory.ClozelHerm.EopV_adjoint | (intros; apply GlobalTheory.CompanionTheory.ClozelHerm.EopV_adjoint <;> assumption)
