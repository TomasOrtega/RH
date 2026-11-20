import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionResidueFieldSurjective
import Mathlib
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FClosedImmersionResidueFieldSurjective.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.closedImmersion_residueField_surjective : ∀ (X Y : AlgebraicGeometry.Scheme.{0}) (i : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion i] (x : X), Function.Surjective (i.residueFieldMap x).hom := by
  first | exact @GlobalTheory.residueFieldMap_surjective_of_isClosedImmersion | exact GlobalTheory.residueFieldMap_surjective_of_isClosedImmersion | (intros; apply GlobalTheory.residueFieldMap_surjective_of_isClosedImmersion <;> assumption)
