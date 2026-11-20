import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureOperatorFacts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.closure_operator_facts : PositivityTheory.RgBcC.Fc.ClsFacts := by
  first | exact @GlobalTheory.CompanionTheory.FcCls.clsFacts | exact GlobalTheory.CompanionTheory.FcCls.clsFacts | (intros; apply GlobalTheory.CompanionTheory.FcCls.clsFacts <;> assumption)
