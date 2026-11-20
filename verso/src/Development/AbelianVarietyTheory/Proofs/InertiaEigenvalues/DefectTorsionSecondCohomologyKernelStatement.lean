import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefectTorsionSecondCohomologyKernel
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NL.DefectTorsion.defect_torsion` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDefectTorsionSecondCohomologyKernel.lean&line=346#L346)
-/
theorem _root_.GlobalTheory.T.defect_torsion_second_cohomology_kernel : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Pr2d D HW F := by
  first | exact @GlobalTheory.NL.DefectTorsion.defect_torsion | exact GlobalTheory.NL.DefectTorsion.defect_torsion | (intros; apply GlobalTheory.NL.DefectTorsion.defect_torsion <;> assumption)
