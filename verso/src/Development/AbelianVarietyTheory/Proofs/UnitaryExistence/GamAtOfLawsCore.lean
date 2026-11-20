import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruenceStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.RunIn

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem gamAt_of_lawsCore' : ∀ (D : D7) (T : Core D), LawsCore T → GlobalTheory.RunIn.GamAt T :=
  fun D T h j hj σ hσ => GlobalTheory.T.coreArithmeticGroup_contains_principalCongruence D T h j hj σ hσ

end GlobalTheory.RunIn
