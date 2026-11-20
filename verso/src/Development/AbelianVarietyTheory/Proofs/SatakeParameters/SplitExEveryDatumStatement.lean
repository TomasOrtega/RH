import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct
open Formalism.BasicNotions NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.splitEx_every_datum : ∀ D : D7, Formalism.L2.SplitEx D := by
  first | exact @GlobalTheory.SplitConjPlace.splitEx_all | exact GlobalTheory.SplitConjPlace.splitEx_all | (intros; apply GlobalTheory.SplitConjPlace.splitEx_all <;> assumption)
