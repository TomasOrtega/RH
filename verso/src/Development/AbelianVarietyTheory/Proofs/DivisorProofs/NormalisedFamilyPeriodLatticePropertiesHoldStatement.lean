import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyPeriodLatticePropertiesHold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.normalisedFamily_periodLattice_properties_hold : GlobalTheory.ColNorms.PeriodLattices := by
  first | exact @GlobalTheory.ColNorms.periodLattices | exact GlobalTheory.ColNorms.periodLattices | (intros; apply GlobalTheory.ColNorms.periodLattices <;> assumption)
