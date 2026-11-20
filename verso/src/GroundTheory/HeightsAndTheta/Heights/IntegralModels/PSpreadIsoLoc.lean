import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHom
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadIsoLoc
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomLoc
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomInjLoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

/- English proof (translation)
Introduce `X f _ _ p U F G hF hG β`. Take `⟨m₁, hm₁, hp₁, H₁⟩` from `h₁ X f p U F G hF hG β.hom`. Take `⟨m₂, hm₂, hp₂, H₂⟩` from `h₁ X f p U G F hG hF β.inv`. Take `⟨m₃, hm₃, hp₃, I₃⟩` from `h₂ X f p U F F hF hF`. Take `⟨m₄, hm₄, hp₄, I₄⟩` from `h₂ X f p U G G hG hG`.

Take `⟨n, hn_def⟩ : ∃ n, n = m₁ * m₂ * m₃ * m₄` from `⟨_, rfl⟩`. Establish `hn : 0 < n` using `by rw [hn_def]; positivity`. Establish `hpn : ¬ (p : ℕ) ∣ n`. Rewrite using `[hn_def]`. Simplify using `only [Nat.Prime.dvd_mul p.2]`.

The claim follows by propositional logic. Take `⟨ψ₁, e₁⟩` from `H₁ n hn (Dvd.intro (m₂ * m₃ * m₄) (by rw [hn_def]; ring)) hpn`. Take `⟨ψ₂, e₂⟩` from `H₂ n hn (Dvd.intro (m₁ * m₃ * m₄) (by rw [hn_def]; ring)) hpn`. Establish `k₁ : ψ₁ ≫ ψ₂ = 𝟙 _` using `I₃ n hn (Dvd.intro (m₁ * m₂ * m₄) (by rw [hn_def]; ring)) hpn _ _ (by`. Rewrite using `[pullbackHomAlong_comp, pullbackHomAlong_id, e₁, e₂, ← pullbackHomAlong_comp, Iso.hom_inv_id, pullbackHomAlong_id])`.

Establish `k₂ : ψ₂ ≫ ψ₁ = 𝟙 _` using `I₄ n hn (Dvd.intro (m₁ * m₂ * m₃) (by rw [hn_def]; ring)) hpn _ _ (by`. Rewrite using `[pullbackHomAlong_comp, pullbackHomAlong_id, e₂, e₁, ← pullbackHomAlong_comp, Iso.inv_hom_id, pullbackHomAlong_id])`. Use `⟨n, hn, hpn, ⟨ψ₁, ψ₂, k₁, k₂⟩, Iso.ext ?_⟩` and prove the remaining obligations. Rewrite using `[pullbackIsoAlong_hom, pullbackIsoAlong_hom]`. Conclude with `e₁`.
-/
theorem SpreadIsoLoc.proof (h₁ : SpreadHomLoc.Statement) (h₂ : SpreadHomInjLoc.Statement) :
    SpreadIsoLoc.Statement := by
  intro X f _ _ p U F G hF hG β
  obtain ⟨m₁, hm₁, hp₁, H₁⟩ := h₁ X f p U F G hF hG β.hom
  obtain ⟨m₂, hm₂, hp₂, H₂⟩ := h₁ X f p U G F hG hF β.inv
  obtain ⟨m₃, hm₃, hp₃, I₃⟩ := h₂ X f p U F F hF hF
  obtain ⟨m₄, hm₄, hp₄, I₄⟩ := h₂ X f p U G G hG hG
  obtain ⟨n, hn_def⟩ : ∃ n, n = m₁ * m₂ * m₃ * m₄ := ⟨_, rfl⟩
  have hn : 0 < n := by rw [hn_def]; positivity
  have hpn : ¬ (p : ℕ) ∣ n := by
    rw [hn_def]
    simp only [Nat.Prime.dvd_mul p.2]
    tauto
  obtain ⟨ψ₁, e₁⟩ := H₁ n hn (Dvd.intro (m₂ * m₃ * m₄) (by rw [hn_def]; ring)) hpn
  obtain ⟨ψ₂, e₂⟩ := H₂ n hn (Dvd.intro (m₁ * m₃ * m₄) (by rw [hn_def]; ring)) hpn
  have k₁ : ψ₁ ≫ ψ₂ = 𝟙 _ := I₃ n hn (Dvd.intro (m₁ * m₂ * m₄) (by rw [hn_def]; ring)) hpn _ _ (by
    rw [pullbackHomAlong_comp, pullbackHomAlong_id, e₁, e₂, ← pullbackHomAlong_comp,
      Iso.hom_inv_id, pullbackHomAlong_id])
  have k₂ : ψ₂ ≫ ψ₁ = 𝟙 _ := I₄ n hn (Dvd.intro (m₁ * m₂ * m₃) (by rw [hn_def]; ring)) hpn _ _ (by
    rw [pullbackHomAlong_comp, pullbackHomAlong_id, e₂, e₁, ← pullbackHomAlong_comp,
      Iso.inv_hom_id, pullbackHomAlong_id])
  refine ⟨n, hn, hpn, ⟨ψ₁, ψ₂, k₁, k₂⟩, Iso.ext ?_⟩
  rw [pullbackIsoAlong_hom, pullbackIsoAlong_hom]
  exact e₁

end GroundTheory.Heights₂.Heights.Model
