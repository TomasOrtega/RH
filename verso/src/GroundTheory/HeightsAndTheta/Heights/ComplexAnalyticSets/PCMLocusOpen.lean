import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMLocusOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMProjDimCriterion
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProjDimSpread
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIdealHeightSpread
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Introduce `n I P _ hIP hCM`. Take `⟨ℓ, hℓ, hℓht⟩` from `(hcrit n I P hIP).mp hCM`. Take `⟨g₁, hg₁P, hg₁⟩` from `hpd (MvPolynomial (Fin n) ℂ) I P ℓ hℓ`. Take `⟨g₂, hg₂P, hg₂⟩` from `hht (MvPolynomial (Fin n) ℂ) I P hIP`. Use `⟨g₁ * g₂, fun h => (‹P.IsPrime›.mem_or_mem h).elim hg₁P hg₂P, fun Q _ hIQ hgQ => ?_⟩` and prove the remaining obligations.

Establish `h₁ : g₁ ∉ Q` using `fun h => hgQ (Q.mul_mem_right g₂ h)`. Establish `h₂ : g₂ ∉ Q` using `fun h => hgQ (Q.mul_mem_left g₁ h)`. Conclude with `(hcrit n I Q hIQ).mpr ⟨ℓ, hg₁ Q h₁, hℓht.trans (hg₂ Q hIQ h₂)⟩`.
-/
theorem CMLocusOpen.proof (hcrit : CMProjDimCriterion.Statement) (hpd : ProjDimSpread.Statement)
    (hht : IdealHeightSpread.Statement) : CMLocusOpen.Statement := by
  intro n I P _ hIP hCM
  obtain ⟨ℓ, hℓ, hℓht⟩ := (hcrit n I P hIP).mp hCM
  obtain ⟨g₁, hg₁P, hg₁⟩ := hpd (MvPolynomial (Fin n) ℂ) I P ℓ hℓ
  obtain ⟨g₂, hg₂P, hg₂⟩ := hht (MvPolynomial (Fin n) ℂ) I P hIP
  refine ⟨g₁ * g₂, fun h => (‹P.IsPrime›.mem_or_mem h).elim hg₁P hg₂P, fun Q _ hIQ hgQ => ?_⟩
  have h₁ : g₁ ∉ Q := fun h => hgQ (Q.mul_mem_right g₂ h)
  have h₂ : g₂ ∉ Q := fun h => hgQ (Q.mul_mem_left g₁ h)
  exact (hcrit n I Q hIQ).mpr ⟨ℓ, hg₁ Q h₁, hℓht.trans (hg₂ Q hIQ h₂)⟩

end GroundTheory.Heights₂.Heights
