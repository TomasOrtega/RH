import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagRelevant
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalRelevant

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem X_mem_ker_iff {K : Type} {ι : K → Type} {Φ : Type} [Field Φ] (c : (Σ k, ι k) → Φ)
    (p : Σ k, ι k) :
    (X p : MvPolynomial (Σ k, ι k) ℤ) ∈ RingHom.ker (T.multiConeMap c) ↔ c p = 0 := by
  rw [RingHom.mem_ker]
  unfold T.multiConeMap
  rw [eval₂Hom_X', mul_eq_zero, C_eq_zero]
  simp [X_ne_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lineVal_ne_zero {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
    [Algebra Ω Φ] (e : Module.Basis (Fin 2) Ω E) {ψ : E →ₗ[Ω] Ω} (hψ : ψ ≠ 0) {a : Φ}
    (ha : Transcendental Ω a) : T.lineVal e ψ a ≠ 0 := by
  intro h
  unfold T.lineVal at h
  by_cases h1 : ψ (e 1) = 0
  · apply hψ
    refine e.ext fun q => ?_
    fin_cases q
    · simp only [h1, map_zero, mul_zero, add_zero] at h
      simpa using (map_eq_zero_iff _ (algebraMap Ω Φ).injective).1 h
    · simpa using h1
  · apply ha
    have h1' : algebraMap Ω Φ (ψ (e 1)) ≠ 0 := (map_ne_zero _).2 h1
    have : a = algebraMap Ω Φ (-(ψ (e 0)) / ψ (e 1)) := by
      rw [map_div₀, map_neg, eq_div_iff h1']
      linear_combination h
    rw [this]
    exact isAlgebraic_algebraMap _

end DiagonalRelevant

open DiagonalRelevant DiagonalForms in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem DiagRelevant.proof : DiagRelevant.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ _ hgen hdet ⟨i, hi⟩ a ha
  have hmap : ∀ y : Ω, y ≠ 0 → algebraMap Ω Φ y ≠ 0 := fun y hy => (map_ne_zero _).2 hy
  obtain ⟨u, hu, w, hw, huw⟩ := exists_detE_ne B i hi e
  obtain ⟨l, hl⟩ : ∃ l, δ l ≠ 0 := by
    by_contra! h
    exact huw ((Submodule.mem_bot _).1 ((Submodule.span_le (p := ⊥)).2
      (by rintro _ ⟨l, rfl⟩; simp [h l]) ((hdet i hi).2 u hu w hw)))
  obtain ⟨ψ₀, hψ₀, ψ₁, -, hne⟩ := exists_dual_pair B i hi e
  obtain ⟨k, hk⟩ : ∃ k, φ k ≠ 0 := by
    by_contra! h
    obtain ⟨c, -, hc⟩ := hgen i hi ψ₀ hψ₀
    exact hne (by simp [hc, h])
  have hv : T.lineVal e (φ k) (a 0) ≠ 0 := lineVal_ne_zero e hk (ha.transcendental 0)
  intro blk
  cases blk with
  | base => exact ⟨i, fun h => hmap _ hi ((X_mem_ker_iff _ _).1 h)⟩
  | det => exact ⟨l, fun h => hmap _ hl ((X_mem_ker_iff _ _).1 h)⟩
  | line0 => exact ⟨k, fun h => hv ((X_mem_ker_iff _ _).1 h)⟩
  | line1 => exact ⟨k, fun h => hv ((X_mem_ker_iff _ _).1 h)⟩

end

end GroundTheory.Heights₂.Heights.Inter
