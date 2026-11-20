import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodORingOfIntegers

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.LitGood

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem litGoodO : LitGoodO :=
  fun l _ LL => GlobalTheory.Pass.goodO_ringOfIntegers l LL

end GlobalTheory.LitGood
