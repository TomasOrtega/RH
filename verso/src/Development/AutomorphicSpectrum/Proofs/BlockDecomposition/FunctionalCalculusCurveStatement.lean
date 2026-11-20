import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusCurve
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.WaveCurve.fcurve | exact GlobalTheory.CompanionTheory.WaveCurve.fcurve | (intros; apply GlobalTheory.CompanionTheory.WaveCurve.fcurve <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.functional_calculus_curve : PositivityTheory.RgBcC.Fc.Fcurve := by
  first | exact @GlobalTheory.CompanionTheory.WaveCurve.fcurve | exact GlobalTheory.CompanionTheory.WaveCurve.fcurve | (intros; apply GlobalTheory.CompanionTheory.WaveCurve.fcurve <;> assumption)
