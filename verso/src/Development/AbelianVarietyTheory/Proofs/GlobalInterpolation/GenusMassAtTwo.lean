import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdAll

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem genusMassAt_two : ∀ D : Formalism.BasicNotions.D7, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.GenusMassAt D 2 :=
  fun D => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.genusMassAt_of D (genusMassStd_all D) 2

end GlobalTheory
