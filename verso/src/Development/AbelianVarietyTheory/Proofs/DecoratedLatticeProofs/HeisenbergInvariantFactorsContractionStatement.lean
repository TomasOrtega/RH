import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergInvariantFactorsContraction
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.heisenbergInvariant_factors_contraction : GlobalTheory.LocFlat.ContrFactor := by
  first | exact @GlobalTheory.LocFlat.contrFactor | exact GlobalTheory.LocFlat.contrFactor | (intros; apply GlobalTheory.LocFlat.contrFactor <;> assumption)
