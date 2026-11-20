import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
import Mathlib
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FResidueFieldMapFiniteOfQuasiFinite.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.residueFieldMap_finite_of_quasiFinite : ∀ {Y Z : Scheme.{0}} (g : Y ⟶ Z) [LocallyQuasiFinite g] (y : Y), (g.residueFieldMap y).hom.Finite := by
  first | exact @GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite | exact GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite | (intros; apply GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite <;> assumption)
