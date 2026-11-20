import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeUsedPropertiesOfAdmitted
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWachLatticeUsedPropertiesOfAdmitted.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.wachLattice_usedProperties_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), tableLineDegreeTwo.admitted D HW F Cm → ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), GlobalTheory.WachUse.QN ((HW l).W K 1 LL hA.2.2) := by
  first | exact @GlobalTheory.WachQN.qN_of_admitted | exact GlobalTheory.WachQN.qN_of_admitted | (intros; apply GlobalTheory.WachQN.qN_of_admitted <;> assumption)
