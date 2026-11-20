import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagShiftTotalLinRootPower
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Top.Sh_Tot_linRoot_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FFlagShiftTotalLinRootPower.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.flag_shift_total_lin_root_power : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ : Ψ) (u : Wt Ψ N), Sh j τ (linRoot u ^ (dimFl Ψ N + 1)) = -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u τ i) ∧ Tot τ (linRoot u ^ (dimFl Ψ N + 1)) = -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i, u τ i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.Sh_Tot_linRoot_pow | exact GlobalTheory.CompanionTheory.Ar.Top.Sh_Tot_linRoot_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.Sh_Tot_linRoot_pow <;> assumption)
