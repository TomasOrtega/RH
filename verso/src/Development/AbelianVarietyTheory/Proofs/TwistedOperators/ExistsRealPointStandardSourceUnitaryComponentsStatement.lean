import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPointStandardSourceUnitaryComponents
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeries
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormRationality
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StdRealLift.exists_real_point` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsRealPointStandardSourceUnitaryComponents.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.exists_realPoint_standardSource_unitaryComponents : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (v : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, (v τ)ᴴ * v τ = 1) → ∃ h ∈ GinfC S, ∀ τ, compAt C.θ τ (mt S h) = v τ := by
  first | exact @GlobalTheory.StdRealLift.exists_real_point | exact GlobalTheory.StdRealLift.exists_real_point | (intros; apply GlobalTheory.StdRealLift.exists_real_point <;> assumption)
