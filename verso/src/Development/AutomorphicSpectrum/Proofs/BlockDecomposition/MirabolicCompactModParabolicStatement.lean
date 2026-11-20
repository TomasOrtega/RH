import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCompactModParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMirabolicCompactModParabolic.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.mirabolic_compact_mod_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ), ∃ C : Set (Mir k ((i + 1) + t)), IsCompact C ∧ ∀ g : Mir k ((i + 1) + t), ∃ h ∈ MirabolicParabolic k (i + 1) t, ∃ c ∈ C, g = h * c := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Coc.hgp_cocompact | exact GlobalTheory.CompanionTheory.BZPhiPG.Coc.hgp_cocompact | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Coc.hgp_cocompact <;> assumption)
