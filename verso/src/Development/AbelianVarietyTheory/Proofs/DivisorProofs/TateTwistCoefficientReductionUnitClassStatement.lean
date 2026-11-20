import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCoefficientReductionUnitClass
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.EtC.red_one`. Consider the case `exact GlobalTheory.EtC.red_one`. Consider the case `(intros; apply GlobalTheory.EtC.red_one <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.tateTwistCoefficientReduction_unitClass : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → red Q q E 0 0 (one Q E) = one q E := by
  first
  | exact @GlobalTheory.EtC.red_one
  | exact GlobalTheory.EtC.red_one
  | (intros; apply GlobalTheory.EtC.red_one <;> assumption)
