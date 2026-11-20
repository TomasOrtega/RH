import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsFinitelyOverSchemeOfIsEmptyPullback
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.splitsFinitelyOverScheme_of_isEmpty_pullback : ∀ {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X), IsEmpty (pullback f y : Scheme.{0}) → GlobalTheory.EtC.Tr.Splits f y := by
  first | (exact @GlobalTheory.EtC.Tr.splits_of_isEmpty_pullback) | (exact GlobalTheory.EtC.Tr.splits_of_isEmpty_pullback) | (intros; apply GlobalTheory.EtC.Tr.splits_of_isEmpty_pullback  <;> assumption)
