import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityReductionDiagonalProd
import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SiegLoc.NuDiag.nuAt_eq_prod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMultiplicityReductionDiagonalProd.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.multiplicity_reduction_diagonal_prod : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R), σ ϖ = ϖ → (∀ a, σ (σ a) = a) → ∀ (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (n : ℕ) (h g g' : Matrix (Fin n) (Fin n) R) (d : Fin n → R), g * g' = 1 → g' * g = 1 → cT σ g * h * g = Matrix.diagonal d → nuAt ϖ (red ϖ k h) = ∏ i : Fin n, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) (d i)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.NuDiag.nuAt_eq_prod | exact GlobalTheory.CompanionTheory.SiegLoc.NuDiag.nuAt_eq_prod | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.NuDiag.nuAt_eq_prod <;> assumption)
