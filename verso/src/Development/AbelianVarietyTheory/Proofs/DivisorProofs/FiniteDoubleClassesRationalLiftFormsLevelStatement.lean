import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleClassesRationalLiftFormsLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteDoubleClassesRationalLiftFormsLevel.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.finiteDoubleClasses_rational_liftFormsLevel : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T),
    ClassesAt p j t := by
  first | exact @GlobalTheory.FrameOf.classesAt | exact GlobalTheory.FrameOf.classesAt | (intros; apply GlobalTheory.FrameOf.classesAt <;> assumption)
