import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualModuleFiniteProjective

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FDualModuleFiniteProjective.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.dual_module_finite_projective : ∀ (R P : Type) [CommRing R] (f : R) [AddCommGroup P] [Module R P]
  [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P] [Module.Finite (Localization.Away f) P]
  [Module.Projective (Localization.Away f) P],
  Module.Finite (Localization.Away f) (P →ₗ[R] Localization.Away f) ∧ Module.Projective (Localization.Away f) (P →ₗ[R] Localization.Away f) := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.HomDual.finite_projective_hom | exact GlobalTheory.CompanionTheory.Ggeo.HomDual.finite_projective_hom | (intros; apply GlobalTheory.CompanionTheory.Ggeo.HomDual.finite_projective_hom <;> assumption)
