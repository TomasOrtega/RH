import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeftMulUnitaryMatrixAddHaar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Twist.LeftHaar.integral_left_unitary` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIntegralLeftMulUnitaryMatrixAddHaar.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.integral_leftMul_unitaryMatrix_addHaar : ∀ (D : D7) (W : HSp D) (r : ℕ) (h : GA D W) (ν : Measure (Mx D W.rank r)), ν.IsAddHaarMeasure → ∀ Φ : Mx D W.rank r → ℂ, ∫ y, Φ (HMul.hMul (Formalism.L2.Theta.mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r) ∂ν = ∫ y, Φ y ∂ν := by
  first | exact @GlobalTheory.Twist.LeftHaar.integral_left_unitary | exact GlobalTheory.Twist.LeftHaar.integral_left_unitary | (intros; apply GlobalTheory.Twist.LeftHaar.integral_left_unitary <;> assumption)
