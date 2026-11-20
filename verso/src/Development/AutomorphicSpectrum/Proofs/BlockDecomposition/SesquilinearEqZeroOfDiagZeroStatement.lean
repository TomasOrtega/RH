import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SesquilinearEqZeroOfDiagZero
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSesquilinearEqZeroOfDiagZero.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.sesquilinear_eq_zero_of_diag_zero : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v, B v v = 0) → B = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero | exact GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero <;> assumption)
