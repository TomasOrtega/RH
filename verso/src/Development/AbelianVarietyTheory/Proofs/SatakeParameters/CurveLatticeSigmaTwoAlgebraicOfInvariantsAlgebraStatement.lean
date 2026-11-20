import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CurveLatticeSigmaTwoAlgebraicOfInvariantsAlgebra
import Formalism.LocalToGlobal.InertKernelTheory.DefsSigma
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CurveSigmaAlg.secondEisensteinAlgebraic_of_invAlg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FCurveLatticeSigmaTwoAlgebraicOfInvariantsAlgebra.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.curveLattice_sigmaTwo_algebraic_of_invariants_algebraic : Formalism.L2.KerInert.Sigma.InvAlg → Formalism.L2.KerInert.Sigma.SecondEisensteinAlgebraic := by
  first | exact @GlobalTheory.CurveSigmaAlg.secondEisensteinAlgebraic_of_invAlg | exact GlobalTheory.CurveSigmaAlg.secondEisensteinAlgebraic_of_invAlg | (intros; apply GlobalTheory.CurveSigmaAlg.secondEisensteinAlgebraic_of_invAlg <;> assumption)
