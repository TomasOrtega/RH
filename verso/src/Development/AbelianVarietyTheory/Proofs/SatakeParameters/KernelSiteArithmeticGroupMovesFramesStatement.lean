import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteArithmeticGroupMovesFrames
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FKernelSiteArithmeticGroupMovesFrames.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.kernelSite_arithmeticGroup_moves_frames : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Move) := by
  first | exact @GlobalTheory.TwV.move_at_site | exact GlobalTheory.TwV.move_at_site | (intros; apply GlobalTheory.TwV.move_at_site <;> assumption)
