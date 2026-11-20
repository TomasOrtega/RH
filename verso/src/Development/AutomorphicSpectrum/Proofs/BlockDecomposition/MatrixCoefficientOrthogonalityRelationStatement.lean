import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientOrthogonalityRelation
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulInner
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMatrixCoefficientOrthogonalityRelation.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.matrix_coefficient_orthogonality_relation : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (hσ : IsU σ), IsU ρ → ∀ (v : B) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν),
    IsSelfAdjoint (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeA.isSelfAdjoint_coefOp | exact GlobalTheory.CompanionTheory.RgHeA.isSelfAdjoint_coefOp | (intros; apply GlobalTheory.CompanionTheory.RgHeA.isSelfAdjoint_coefOp <;> assumption)
