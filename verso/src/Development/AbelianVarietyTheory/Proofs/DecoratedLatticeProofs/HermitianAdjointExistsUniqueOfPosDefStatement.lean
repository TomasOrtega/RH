import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointExistsUniqueOfPosDef
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.hermitian_adjoint_exists_unique` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FHermitianAdjointExistsUniqueOfPosDef.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.hermitian_adjoint_exists_unique_of_posDef : ∀ (A C : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C] (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ), (∀ x y, ip x y = conj (ip y x)) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → ∀ (io : C →ₗ[ℂ] A) (u : A), ∃! x : C, ∀ y, ip y x = ipA (io y) u := by
  first | exact @GlobalTheory.hermitian_adjoint_exists_unique | exact GlobalTheory.hermitian_adjoint_exists_unique | (intros; apply GlobalTheory.hermitian_adjoint_exists_unique <;> assumption)
