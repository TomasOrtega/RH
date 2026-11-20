import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolic
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnipotentTopMemParabolic.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.unipotent_top_mem_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (x : Fin i → k), ∃ h : uM k (i + t) (topV k i t x) ∈ HPG k i t, pgProj k i t ⟨_, h⟩ = (uM k i x, 1) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.TopCol.main | exact GlobalTheory.CompanionTheory.BZPsiPG.TopCol.main | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.TopCol.main <;> assumption)
