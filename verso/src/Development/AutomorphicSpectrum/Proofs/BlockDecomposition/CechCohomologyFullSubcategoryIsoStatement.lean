import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechCohomologyFullSubcategoryIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.CechAugRowU
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
universe u v w
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CechFull.cechH_fullSubcategory_H` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCechCohomologyFullSubcategoryIso.lean&line=120#L120)
-/
theorem _root_.GlobalTheory.T.cech_cohomology_full_subcategory_iso : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) (Q : ObjectProperty C) {ι : Type} (W : ι → ObjectProperty C), (∀ α, W α ≤ Q) → ∀ q p, Nonempty ((cechH (Q.ι ⋙ F) (fun α (T : Q.FullSubcategory) => W α T.obj) q).cx.H p ≃ₗ[R] (cechH F W q).cx.H p) := by
  first | exact @GlobalTheory.CompanionTheory.CechFull.cechH_fullSubcategory_H | exact GlobalTheory.CompanionTheory.CechFull.cechH_fullSubcategory_H | (intros; apply GlobalTheory.CompanionTheory.CechFull.cechH_fullSubcategory_H <;> assumption)
