import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmallFrameAtColumn
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SmallExact.smallHas_of_rayField` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FSmallFrameAtColumn.lean&line=126#L126)
-/
theorem _root_.GlobalTheory.T.small_frame_at_column : GlobalTheory.NT.RayField → ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SmallHas (w.D Z) (Fr.at (w.st Z) f) := by
  first | exact @GlobalTheory.SmallExact.smallHas_of_rayField | exact GlobalTheory.SmallExact.smallHas_of_rayField | (intros; apply GlobalTheory.SmallExact.smallHas_of_rayField <;> assumption)
