import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreClosureModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsTwistedDualGensExist
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsGenericProjClosureDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsGenericProjClosureDivisor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB Φ _ _ _ _ e t ht`. Take `⟨a₁, ha₁⟩` from `h₁ O Ω K ι y N E B`. Take `⟨M, φ, hφ⟩` from `ha₁ a₁ le_rfl`. Take `⟨a₁', ha₁'⟩` from `h₁ O Ω K ι y N E B'`. Take `⟨M', φ', hφ'⟩` from `ha₁' a₁' le_rfl`.

Establish `hZ` using `h₂ O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₁ a₁' φ φ' hφ hφ' Φ e t ht`. Take `⟨f₀, g₀, hD, hfg⟩` from `h₃ O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₁ a₁' φ φ' hφ hφ' Φ e t ht hZ`. Conclude with `⟨M, M', a₁, a₁', φ, φ', hφ, hφ', hZ, f₀, g₀, hD, hfg⟩`.
-/
theorem GenericProjClosureModel.proof (h₁ : TwistedDualGensExist.Statement)
    (h₂ : GenericProjClosureDim.Statement) (h₃ : GenericProjClosureDivisor.Statement) :
    GenericProjClosureModel.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB Φ _ _ _ _ e t ht
  obtain ⟨a₁, ha₁⟩ := h₁ O Ω K ι y N E B
  obtain ⟨M, φ, hφ⟩ := ha₁ a₁ le_rfl
  obtain ⟨a₁', ha₁'⟩ := h₁ O Ω K ι y N E B'
  obtain ⟨M', φ', hφ'⟩ := ha₁' a₁' le_rfl
  have hZ := h₂ O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₁ a₁' φ φ' hφ hφ' Φ e t ht
  obtain ⟨f₀, g₀, hD, hfg⟩ :=
    h₃ O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₁ a₁' φ φ' hφ hφ' Φ e t ht hZ
  exact ⟨M, M', a₁, a₁', φ, φ', hφ, hφ', hZ, f₀, g₀, hD, hfg⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
