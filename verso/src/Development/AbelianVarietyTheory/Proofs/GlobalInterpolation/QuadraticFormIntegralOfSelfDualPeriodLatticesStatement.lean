import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticFormIntegralOfSelfDualPeriodLattices
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaMove.qIntAll_of_latAll` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FQuadraticFormIntegralOfSelfDualPeriodLattices.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.quadraticForm_integral_of_selfDual_periodLattices : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), B.LatAll → B.QIntAll := by
  first | exact @GlobalTheory.ThetaMove.qIntAll_of_latAll | exact GlobalTheory.ThetaMove.qIntAll_of_latAll | (intros; apply GlobalTheory.ThetaMove.qIntAll_of_latAll <;> assumption)
