import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFractionRingStalkGeneric
import Mathlib
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.residueField_isFractionRing_of_generic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsFractionRingStalkGeneric.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.isFractionRing_stalk_generic : ∀ (X : Scheme.{0}) (x ξ : X) (e : ξ ⤳ x), IsDomain (X.presheaf.stalk x) → (∀ y, y ⤳ ξ → y = ξ) → @IsFractionRing (X.presheaf.stalk x) _ (X.residueField ξ) _ (RingHom.toAlgebra (X.presheaf.stalkSpecializes e ≫ X.residue ξ).hom) := by
  first | exact @GlobalTheory.residueField_isFractionRing_of_generic | exact GlobalTheory.residueField_isFractionRing_of_generic | (intros; apply GlobalTheory.residueField_isFractionRing_of_generic <;> assumption)
