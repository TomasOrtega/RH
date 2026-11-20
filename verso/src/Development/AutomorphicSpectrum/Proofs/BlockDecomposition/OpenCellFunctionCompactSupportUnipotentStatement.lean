import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellFunctionCompactSupportUnipotent
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalDecompositionNormalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellUnipotentUniquenessClosedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorCompactUnipotentFixerStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FOpenCellFunctionCompactSupportUnipotent.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.open_cell_function_compact_support_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∀ f ∈ openFns d hd ρ, ∃ L : Subgroup (GL (Fin N) k), L ≤ unipU k d hd ∧ IsCompact (L : Set (GL (Fin N) k)) ∧ (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L) ∧ ∀ g, f.1.1 g ≠ 0 → ∃ p ∈ parab k (stdBlocks d hd), ∃ u ∈ L, g = p * pm k (wOpen d hd) * u := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support | exact GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support | (intros; apply GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support <;> assumption)
