import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceDecompositionInternal
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.isInternal_eigSp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FEigenspaceDecompositionInternal.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.eigenspace_decomposition_internal : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (E : Type) [AddCommGroup E] [Module Ω E] (F : Type) [Field F] [NumberField F] (ρ : NumberField.RingOfIntegers F →+* Module.End Ω E) (I : Type) [Fintype I] [DecidableEq I] (σ : I → (NumberField.RingOfIntegers F →+* Ω)), Function.Injective σ → Fintype.card I = Module.finrank ℚ F → DirectSum.IsInternal fun s => eigSp ρ (σ s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isInternal_eigSp | exact GlobalTheory.CompanionTheory.Ar.isInternal_eigSp | (intros; apply GlobalTheory.CompanionTheory.Ar.isInternal_eigSp <;> assumption)
