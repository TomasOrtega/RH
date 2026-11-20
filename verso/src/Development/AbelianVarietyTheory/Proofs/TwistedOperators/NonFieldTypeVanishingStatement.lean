import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonFieldTypeVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.non_field_type_vanishing : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.NonFieldTypeVanishing := by
  first | exact @GlobalTheory.NonFieldType.nonFieldTypeVanishing | exact GlobalTheory.NonFieldType.nonFieldTypeVanishing | (intros; apply GlobalTheory.NonFieldType.nonFieldTypeVanishing <;> assumption)
