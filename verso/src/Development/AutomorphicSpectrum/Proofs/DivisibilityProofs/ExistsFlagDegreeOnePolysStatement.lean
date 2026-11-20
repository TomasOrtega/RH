import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsFlagDegreeOnePolys
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Top.testForms_sh_tot` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FExistsFlagDegreeOnePolys.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_flag_degree_one_polys : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ : Ψ), 1 ≤ j → j < N → (∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N) ∧ degFl Q = 1) ∧ ∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N - 1) ∧ degFl (pkLow j τ 1 * Q) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.testForms_sh_tot | exact GlobalTheory.CompanionTheory.Ar.Top.testForms_sh_tot | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.testForms_sh_tot <;> assumption)
