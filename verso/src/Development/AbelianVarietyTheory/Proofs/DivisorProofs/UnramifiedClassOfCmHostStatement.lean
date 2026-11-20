import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedClassOfCmHost
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnramifiedClassOfCmHost.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.unramified_class_of_cm_host : ∀ D : D7, letI : IsCMField D.host.E := D.host.isCMField_hostE; GlobalTheory.UCls.Unr D.host.E := by
  first | exact @GlobalTheory.MassLink.host_unr | exact GlobalTheory.MassLink.host_unr | (intros; apply GlobalTheory.MassLink.host_unr <;> assumption)
