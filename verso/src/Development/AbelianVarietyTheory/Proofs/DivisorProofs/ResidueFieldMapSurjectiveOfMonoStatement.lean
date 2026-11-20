import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldMapSurjectiveOfMono
import Mathlib
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.residueFieldMap_surjective_of_mono` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FResidueFieldMapSurjectiveOfMono.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.residueFieldMap_surjective_of_mono' : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [Mono f] (x : X), Function.Surjective (f.residueFieldMap x).hom := by
  first | exact @GlobalTheory.residueFieldMap_surjective_of_mono | exact GlobalTheory.residueFieldMap_surjective_of_mono | (intros; apply GlobalTheory.residueFieldMap_surjective_of_mono <;> assumption)
