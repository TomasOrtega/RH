import Formalism.SharpRestriction.Divisibility.ChainOperators.WeightFramesOfSubgroupFrames
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GenFrameSB

open Formalism.BasicNotions

namespace Formalism.MainNotions.DIV.Lemmas

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cutKW_holds : CutKW.KW := kw_of_cutSB coeffNormLE_iff_spanNormLE_of_hasCompl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.
-/
theorem theta_isometry_facts_hold (D : D7) : Formalism.MainNotions.OrbitPlaces.ConclusionW D := by
  intro l _ N0 N1 nu Th B
  apply cutKW_holds

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.
-/
theorem generic_frames_letters : Formalism.MainNotions.product_zeroth_first_parts.Conclusion4 := by
  intro l _ d _ N0 N1 nu Th B
  apply cutKW_holds

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem stmtW_holds (D : D7) : Formalism.MainNotions.OrbitPlaces.WeightsFromStandardBasis D := fun _ => theta_isometry_facts_hold D

end Formalism.MainNotions.DIV.Lemmas
