import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalDecompositionNormal
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnipotentRadicalDecompositionNormal.lean&line=126#L126)
-/
theorem _root_.GlobalTheory.T.unipotent_radical_decomposition_normal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ n ∈ unipB k (Fin N), ∃ a ∈ unipL k d hd, ∃ u ∈ unipU k d hd, n = a * u) ∧ ∀ n ∈ unipB k (Fin N), ∀ u ∈ unipU k d hd, n * u * n⁻¹ ∈ unipU k d hd := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad | exact GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad | (intros; apply GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad <;> assumption)
