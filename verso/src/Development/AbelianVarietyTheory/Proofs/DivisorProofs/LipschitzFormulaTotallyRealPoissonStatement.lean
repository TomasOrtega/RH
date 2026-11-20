import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LipschitzFormulaTotallyRealPoisson
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.LipschitzTR.lipschitz | exact GlobalTheory.LipschitzTR.lipschitz | (intros; apply GlobalTheory.LipschitzTR.lipschitz <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.lipschitz_formula_totally_real_poisson : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz := by
  first | exact @GlobalTheory.LipschitzTR.lipschitz | exact GlobalTheory.LipschitzTR.lipschitz | (intros; apply GlobalTheory.LipschitzTR.lipschitz <;> assumption)
