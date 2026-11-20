import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoordIdealXgen
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem SerreVanish.equiv (hC : GradedCech.Statement) :
    Kleiman.SerreVanish.Statement.{0, 0} ↔ IndefiniteRowSideFullHecke.Kleiman.SerreVanish.Statement := by
  constructor
  · intro hA S _ _ N M _ _ _ _ G hfin
    obtain ⟨c₀, hc₀⟩ := hA S N M (gradedEquiv S N M G) hfin
    obtain ⟨e, -, -⟩ := hC S N
    refine ⟨c₀, fun i hi c hc => ?_⟩
    have := hc₀ i hi c hc
    exact (e M G i c).injective.subsingleton
  · intro hB S _ _ N M _ _ _ _ 𝓜 hfin
    obtain ⟨G, rfl⟩ := (gradedEquiv S N M).surjective 𝓜
    obtain ⟨c₀, hc₀⟩ := hB S N M G hfin
    obtain ⟨e, -, -⟩ := hC S N
    refine ⟨c₀, fun i hi c hc => ?_⟩
    have := hc₀ i hi c hc
    exact (e M G i c).symm.injective.subsingleton

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
