import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

/- English proof (translation)
Introduce `X f _ _ a ha F G hF hG α`. Take `⟨m₁, hm₁, H₁⟩` from `h₁ X f a ha F G hF hG α.hom`. Take `⟨m₂, hm₂, H₂⟩` from `h₁ X f a ha G F hG hF α.inv`. Take `⟨m₃, hm₃, I₃⟩` from `h₂ X f a ha F F hF hF`. Take `⟨m₄, hm₄, I₄⟩` from `h₂ X f a ha G G hG hG`.

Take `⟨n, hn_def⟩ : ∃ n, n = m₁ * m₂ * m₃ * m₄` from `⟨_, rfl⟩`. Establish `hn : 0 < n` using `by rw [hn_def]; positivity`. Take `⟨ψ₁, e₁⟩` from `H₁ n hn (Dvd.intro (m₂ * m₃ * m₄) (by rw [hn_def]; ring))`. Take `⟨ψ₂, e₂⟩` from `H₂ n hn (Dvd.intro (m₁ * m₃ * m₄) (by rw [hn_def]; ring))`. Establish `k₁ : ψ₁ ≫ ψ₂ = 𝟙 _` using `I₃ n hn (Dvd.intro (m₁ * m₂ * m₄) (by rw [hn_def]; ring)) _ _ (by`.

Rewrite using `[pullbackHomAlong_comp, pullbackHomAlong_id, e₁, e₂, Iso.hom_inv_id])`. Establish `k₂ : ψ₂ ≫ ψ₁ = 𝟙 _` using `I₄ n hn (Dvd.intro (m₁ * m₂ * m₃) (by rw [hn_def]; ring)) _ _ (by`. Rewrite using `[pullbackHomAlong_comp, pullbackHomAlong_id, e₂, e₁, Iso.inv_hom_id])`. Use `⟨n, hn, ⟨ψ₁, ψ₂, k₁, k₂⟩, Iso.ext ?_⟩` and prove the remaining obligations. Rewrite using `[pullbackIsoAlong_hom]`.

Conclude with `e₁`.
-/
theorem SpreadIso.proof (h₁ : SpreadHom.Statement) (h₂ : SpreadHomInj.Statement) :
    SpreadIso.Statement := by
  intro X f _ _ a ha F G hF hG α
  obtain ⟨m₁, hm₁, H₁⟩ := h₁ X f a ha F G hF hG α.hom
  obtain ⟨m₂, hm₂, H₂⟩ := h₁ X f a ha G F hG hF α.inv
  obtain ⟨m₃, hm₃, I₃⟩ := h₂ X f a ha F F hF hF
  obtain ⟨m₄, hm₄, I₄⟩ := h₂ X f a ha G G hG hG
  obtain ⟨n, hn_def⟩ : ∃ n, n = m₁ * m₂ * m₃ * m₄ := ⟨_, rfl⟩
  have hn : 0 < n := by rw [hn_def]; positivity
  obtain ⟨ψ₁, e₁⟩ := H₁ n hn (Dvd.intro (m₂ * m₃ * m₄) (by rw [hn_def]; ring))
  obtain ⟨ψ₂, e₂⟩ := H₂ n hn (Dvd.intro (m₁ * m₃ * m₄) (by rw [hn_def]; ring))
  have k₁ : ψ₁ ≫ ψ₂ = 𝟙 _ := I₃ n hn (Dvd.intro (m₁ * m₂ * m₄) (by rw [hn_def]; ring)) _ _ (by
    rw [pullbackHomAlong_comp, pullbackHomAlong_id, e₁, e₂, Iso.hom_inv_id])
  have k₂ : ψ₂ ≫ ψ₁ = 𝟙 _ := I₄ n hn (Dvd.intro (m₁ * m₂ * m₃) (by rw [hn_def]; ring)) _ _ (by
    rw [pullbackHomAlong_comp, pullbackHomAlong_id, e₂, e₁, Iso.inv_hom_id])
  refine ⟨n, hn, ⟨ψ₁, ψ₂, k₁, k₂⟩, Iso.ext ?_⟩
  rw [pullbackIsoAlong_hom]
  exact e₁

end GroundTheory.Heights₂.Heights.Model
