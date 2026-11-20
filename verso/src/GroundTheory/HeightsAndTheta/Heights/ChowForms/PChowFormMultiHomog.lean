import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowFormHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Introduce `_ _ _ _ _ _ hP hf` and use `hf.exists_multiHomog hP`.
-/
theorem chowFormMultiHomog : ChowFormMultiHomog.Statement :=
  fun _ _ _ _ _ _ hP hf => hf.exists_multiHomog hP

/- English proof (translation)
The claim follows from `chowFormMultiHomog`.
-/
theorem ChowFormMultiHomog.proof (_h₁ : ProjNullstellensatz.Statement) :
    ChowFormMultiHomog.Statement :=
  chowFormMultiHomog

end GroundTheory.Heights₂.Heights
