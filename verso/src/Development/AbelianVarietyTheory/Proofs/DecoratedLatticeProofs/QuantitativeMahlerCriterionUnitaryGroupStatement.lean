import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuantitativeMahlerCriterionUnitaryGroup
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.htMin_of_reduced | exact GlobalTheory.htMin_of_reduced | (intros; apply GlobalTheory.htMin_of_reduced <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.quantitativeMahlerCriterion_unitaryGroup : ∀ I : AutInst, HtMin I := by
  first | exact @GlobalTheory.htMin_of_reduced | exact GlobalTheory.htMin_of_reduced | (intros; apply GlobalTheory.htMin_of_reduced <;> assumption)
