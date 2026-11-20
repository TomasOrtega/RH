import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaUnitaryGroupOddResidueOfLie
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.Orbit.unitLemmaGroup_of_lie` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnitLemmaUnitaryGroupOddResidueOfLie.lean&line=143#L143)
-/
theorem _root_.GlobalTheory.T.unitLemma_unitary_group_odd_residue_of_lie : UnitLemmaLie → UnitLemmaGroup := by
  first | exact @GlobalTheory.UnitLemma.Orbit.unitLemmaGroup_of_lie | exact GlobalTheory.UnitLemma.Orbit.unitLemmaGroup_of_lie | (intros; apply GlobalTheory.UnitLemma.Orbit.unitLemmaGroup_of_lie <;> assumption)
