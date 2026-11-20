import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.VanishingCechResidue
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.ResidueFiniteModel
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.ResidueChartTransport
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqCech
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

/- English proof (translation)
The claim follows from `(GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.SerreVanish.equiv GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech.proof).1 GroundTheory.Heights₂.Heights.Kleiman.SerreVanish.full.{0, 0}`.
-/
theorem serreVanishing_graded_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman.SerreVanish.Statement :=
  (GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.SerreVanish.equiv
    GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech.proof).1
    GroundTheory.Heights₂.Heights.Kleiman.SerreVanish.full.{0, 0}

/- English proof (translation)
Introduce `P a ha r x hx b hb`. Take `⟨𝓜⟩` from `hM P a ha r x hx b hb`. Take `⟨c₀, hc₀⟩` from `serreVanishing_graded_holds ℂ r 𝓜.M 𝓜.G 𝓜.finite`. Use `⟨c₀.toNat, fun c hc q φ hφ => hT P a b r x 𝓜 c₀ hc₀ c ?_ q φ hφ⟩` and prove the remaining obligations. Use `Int.self_le_toNat c₀` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem VanishingCechResidue.proof (hM : ResidueFiniteModel.Statement)
    (hT : ResidueChartTransport.Statement) : VanishingCechResidue.Statement := by
  intro P a ha r x hx b hb
  obtain ⟨𝓜⟩ := hM P a ha r x hx b hb
  obtain ⟨c₀, hc₀⟩ := serreVanishing_graded_holds ℂ r 𝓜.M 𝓜.G 𝓜.finite
  refine ⟨c₀.toNat, fun c hc q φ hφ => hT P a b r x 𝓜 c₀ hc₀ c ?_ q φ hφ⟩
  have := Int.self_le_toNat c₀
  omega

end

end GroundTheory.Heights₂.Heights.KeyFormula
