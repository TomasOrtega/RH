import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowFormHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem chowFormMultiHomog : ChowFormMultiHomog.Statement :=
  fun _ _ _ _ _ _ hP hf => hf.exists_multiHomog hP

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ChowFormMultiHomog.proof (_h₁ : ProjNullstellensatz.Statement) :
    ChowFormMultiHomog.Statement :=
  chowFormMultiHomog

end GroundTheory.Heights₂.Heights
