import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModulesGlueCover

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FProjectiveModulesGlueCover.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.projective_modules_glue_cover : ∀ (R E : Type) [CommRing R] [AddCommGroup E] [Module R E] (J : Type) [Finite J] (f : J → R), Ideal.span (Set.range f) = ⊤ →
  ∀ (F : J → Type) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [∀ i, Module (Localization.Away (f i)) (F i)]
    [∀ i, IsScalarTower R (Localization.Away (f i)) (F i)] [∀ i, Module.Finite (Localization.Away (f i)) (F i)]
    [∀ i, Module.Projective (Localization.Away (f i)) (F i)] (φ : ∀ i, E →ₗ[R] F i),
    (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (φ i)) → Module.Finite R E ∧ Module.Projective R E := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.finite_projective_of_isLocalizedModule_cover | exact GlobalTheory.CompanionTheory.Ggeo.finite_projective_of_isLocalizedModule_cover | (intros; apply GlobalTheory.CompanionTheory.Ggeo.finite_projective_of_isLocalizedModule_cover <;> assumption)
