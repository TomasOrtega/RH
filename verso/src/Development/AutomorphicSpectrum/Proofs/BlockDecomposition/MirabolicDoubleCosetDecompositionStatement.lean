import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZPhiPG.Cells.cells` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMirabolicDoubleCosetDecomposition.lean&line=226#L226)
-/
theorem _root_.GlobalTheory.T.mirabolic_double_coset_decomposition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ),
  (∀ p ∈ Cl k i t, ∃ h ∈ HPG k (i + 1) (t + 1), ∃ (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)),
      p = h * dEmb k i t d * sEmb k ((i + 1) + t) m) ∧
  (∀ p, p ∉ Cl k i t → ∃ h ∈ HPG k (i + 1) (t + 1), ∃ (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)),
      p = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) m) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Cells.cells | exact GlobalTheory.CompanionTheory.BZPhiPG.Cells.cells | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Cells.cells <;> assumption)
