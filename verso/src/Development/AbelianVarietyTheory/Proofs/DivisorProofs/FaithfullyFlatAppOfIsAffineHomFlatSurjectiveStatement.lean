import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfullyFlatAppOfIsAffineHomFlatSurjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.faithfullyFlat_app_of_isAffineHom_flat_surjective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFaithfullyFlatAppOfIsAffineHomFlatSurjective.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.faithfullyFlat_app_of_isAffineHom_flat_surjective' : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (V : Y.Opens), IsAffineHom p → Flat p → Surjective p → IsAffineOpen V → (p.app V).hom.FaithfullyFlat := by
  first | exact @GlobalTheory.faithfullyFlat_app_of_isAffineHom_flat_surjective | exact GlobalTheory.faithfullyFlat_app_of_isAffineHom_flat_surjective | (intros; apply GlobalTheory.faithfullyFlat_app_of_isAffineHom_flat_surjective <;> assumption)
