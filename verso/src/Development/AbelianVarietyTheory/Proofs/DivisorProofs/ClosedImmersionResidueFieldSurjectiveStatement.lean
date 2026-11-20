import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionResidueFieldSurjective
import Mathlib
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.residueFieldMap_surjective_of_isClosedImmersion | exact GlobalTheory.residueFieldMap_surjective_of_isClosedImmersion | (intros; apply GlobalTheory.residueFieldMap_surjective_of_isClosedImmersion <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.closedImmersion_residueField_surjective : ∀ (X Y : AlgebraicGeometry.Scheme.{0}) (i : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion i] (x : X), Function.Surjective (i.residueFieldMap x).hom := by
  first | exact @GlobalTheory.residueFieldMap_surjective_of_isClosedImmersion | exact GlobalTheory.residueFieldMap_surjective_of_isClosedImmersion | (intros; apply GlobalTheory.residueFieldMap_surjective_of_isClosedImmersion <;> assumption)
