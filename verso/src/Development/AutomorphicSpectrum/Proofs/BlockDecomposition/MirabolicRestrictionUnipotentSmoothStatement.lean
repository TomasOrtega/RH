import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicRestrictionUnipotentSmooth
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMirabolicRestrictionUnipotentSmooth.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.mirabolic_restriction_unipotent_smooth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V), IsSmooth τ → IsSmooth (τ.comp (unipMir k n)) := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.isSmooth_comp_unipMir | exact GlobalTheory.CompanionTheory.MirFourier.isSmooth_comp_unipMir | (intros; apply GlobalTheory.CompanionTheory.MirFourier.isSmooth_comp_unipMir <;> assumption)
