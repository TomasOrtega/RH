import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorOnFrameAndClassSummandPolynomial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FOperatorOnFrameAndClassSummandPolynomial.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.operatorOnFrame_and_classSummand_polynomial : Formalism.L2.KerInert.SecondKernelDifference.ApplyFrame ∧ Formalism.L2.KerInert.SecondKernelDifference.EntQFrame := by
  first | exact @GlobalTheory.TwV.DelA.applyFrame_and_entQFrame | exact GlobalTheory.TwV.DelA.applyFrame_and_entQFrame | (intros; apply GlobalTheory.TwV.DelA.applyFrame_and_entQFrame <;> assumption)
