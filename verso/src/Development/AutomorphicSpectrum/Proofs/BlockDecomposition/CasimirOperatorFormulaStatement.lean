import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirOperatorFormula
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.Casimir.omFormula | exact GlobalTheory.CompanionTheory.Casimir.omFormula | (intros; apply GlobalTheory.CompanionTheory.Casimir.omFormula <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.casimir_operator_formula : PositivityTheory.RgBcC.Fc.OmFormula := by
  first | exact @GlobalTheory.CompanionTheory.Casimir.omFormula | exact GlobalTheory.CompanionTheory.Casimir.omFormula | (intros; apply GlobalTheory.CompanionTheory.Casimir.omFormula <;> assumption)
