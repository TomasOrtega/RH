import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedCellRightStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Cl_mul_sO` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FClosedCellRightStable.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.closed_cell_right_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ), ∀ p ∈ Cl k i t, ∀ m, p * sO k i t m ∈ Cl k i t := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Cl_mul_sO | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Cl_mul_sO | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Cl_mul_sO <;> assumption)
