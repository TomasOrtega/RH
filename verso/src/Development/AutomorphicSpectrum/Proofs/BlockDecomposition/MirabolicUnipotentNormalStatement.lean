import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicUnipotentNormal
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LeibPhi.UNorm.mirUin_normal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMirabolicUnipotentNormal.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.mirabolic_unipotent_normal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), (MirUin k n).Normal := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.UNorm.mirUin_normal | exact GlobalTheory.CompanionTheory.LeibPhi.UNorm.mirUin_normal | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.UNorm.mirUin_normal <;> assumption)
