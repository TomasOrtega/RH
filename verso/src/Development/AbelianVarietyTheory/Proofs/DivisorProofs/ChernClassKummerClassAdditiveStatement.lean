import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassKummerClassAdditive
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.chernClass_kummerClass_additive : GlobalTheory.EtC.DivisorAdditivity := by
  first | (exact @GlobalTheory.EtC.a6add_holds) | (exact GlobalTheory.EtC.a6add_holds) | (intros; apply GlobalTheory.EtC.a6add_holds  <;> assumption)
