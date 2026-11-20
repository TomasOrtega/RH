import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaAtSmallPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrameOf.kapSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKappaAtSmallPlace.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.kappa_at_small_place : InRange fun _ _ _ _ p j P _ w => SmallAt p j P w → KapAt p j P w := by
  first | exact @GlobalTheory.FrameOf.kapSt | exact GlobalTheory.FrameOf.kapSt | (intros; apply GlobalTheory.FrameOf.kapSt <;> assumption)
