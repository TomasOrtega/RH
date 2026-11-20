import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesPositiveSteps
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FKernelSiteFrameValuesPositiveSteps.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.kernelSite_frameValues_positive_steps : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ j, 1 ≤ j → j < D.R.m → S.Del j) := by
  first | exact @GlobalTheory.TwV.StepDel.del_of_pos | exact GlobalTheory.TwV.StepDel.del_of_pos | (intros; apply GlobalTheory.TwV.StepDel.del_of_pos <;> assumption)
