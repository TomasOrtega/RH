import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsConeAvoid
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionsGeneric
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeAvoidsFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjHomInjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeAvoidsOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeAvoidsExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

/- English proof (translation)
Introduce `n d J hJ hd`. Take `⟨A₀, N, hA₀⟩` from `h₄ n d J hJ hd`. Use `⟨{A | ConeAvoids J A N}, h₃ n d N J, ⟨A₀, hA₀⟩, fun A hA => ?_⟩` and prove the remaining obligations. Establish `hfin : (projHom J A).toRingHom.Finite` using `h₁ n d N J A hA`. Conclude with `⟨h₂ n d J A hJ hd hfin, hfin⟩`.
-/
theorem FiniteProjectionsContainOpen.proof (h₁ : ConeAvoidsFinite.Statement)
    (h₂ : FiniteProjHomInjective.Statement) (h₃ : ConeAvoidsOpen.Statement)
    (h₄ : ConeAvoidsExists.Statement) : FiniteProjectionsContainOpen.Statement := by
  intro n d J hJ hd
  obtain ⟨A₀, N, hA₀⟩ := h₄ n d J hJ hd
  refine ⟨{A | ConeAvoids J A N}, h₃ n d N J, ⟨A₀, hA₀⟩, fun A hA => ?_⟩
  have hfin : (projHom J A).toRingHom.Finite := h₁ n d N J A hA
  exact ⟨h₂ n d J A hJ hd hfin, hfin⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
