import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaOperatorSemisimpleOfConclusions
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.SemisimpleLetterIffForallMem
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FGammaOperatorSemisimpleOfConclusions.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.gamma_operator_semisimple_of_conclusions : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.LiftingTheory.adm19 D HW F := by
  first | exact @GlobalTheory.dss_semisimple_of_used | exact GlobalTheory.dss_semisimple_of_used | (intros; apply GlobalTheory.dss_semisimple_of_used <;> assumption)
