import Formalism.SharpRestriction.GrowthBounds.RootWeights.GeneratedWeightLemmaOfFormulas
import Formalism.SharpRestriction.GrowthBounds.RootWeights.DescendingProdEqFactorialChoose

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem generated_weight_lemma_of_reducibility (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (hV1 : ValuationsAdditive D) : ShaLengthVersionTwo D :=
  generated_weight_lemma_of_formulas D h2 hV1 dividedPower_formula_char_zero binomial_formula_char_zero

end Formalism.MainNotions.G.GLWeightTheory
