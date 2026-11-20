import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainCohomologyNerveHomologyEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCochainCohomologyNerveHomologyEquiv.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.cochain_cohomology_nerve_homology_equiv : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    Nonempty (LinearMap.ker (MainStatements.Hodge.dn F 0) ≃ₗ[R] (nerveCx.obj (toMod F)).homology 0) ∧
      ∀ n, Nonempty (MainStatements.Hodge.Hs F n ≃ₗ[R] (nerveCx.obj (toMod F)).homology (n + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_nerveCx | exact GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_nerveCx | (intros; apply GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_nerveCx <;> assumption)
