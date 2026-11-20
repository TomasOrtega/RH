import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZero
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.eigenCharTwist_holds | exact GlobalTheory.eigenCharTwist_holds | (intros; apply GlobalTheory.eigenCharTwist_holds <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.eigencharacter_of_summand_charZero : EigenCharTwist := by
  first | exact @GlobalTheory.eigenCharTwist_holds | exact GlobalTheory.eigenCharTwist_holds | (intros; apply GlobalTheory.eigenCharTwist_holds <;> assumption)
