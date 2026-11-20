import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods

namespace GlobalTheory.PELU

open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

/- English proof (translation)
Unfold `hermForm`. Establish `e : star (B *ᵥ v) = B.map star *ᵥ star v`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct]`. Rewrite using `[e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]`.
-/
theorem hermForm_pullback_matrix {g : ℕ} (Hm B : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → ℂ) :
    hermForm (Bᵀ * Hm * B.map star) u v = hermForm Hm (B *ᵥ u) (B *ᵥ v) := by
  unfold hermForm
  have e : star (B *ᵥ v) = B.map star *ᵥ star v := by
    ext i
    simp [Matrix.mulVec, dotProduct]
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/- English proof (translation)
Take `⟨h1, h2, h3, h4, Hm, h5, h6, h7⟩` from `hP`. Establish `ev : ∀ x, (h.toLinearMap.toAddMonoidHom.comp P) x = h (P x)` using `fun _ => rfl`. Use `set B : Matrix (Fin g) (Fin g) ℂ := LinearMap.toMatrix' h.symm.toLinearMap with hB`. Establish `hBv : ∀ u, B *ᵥ u = h.symm u` using `fun u => by`. Rewrite using `[hB, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']`.

Both sides reduce to the same expression. Use `⟨fun a x => ?_, ?_, ?_, ?_, Bᵀ * Hm * B.map star, ?_, fun z hz => ?_, fun x y => ?_⟩` and prove the remaining obligations. Rewrite using `[ev, ev, h1, hh]`. Conclude with `h.injective.comp h2`. Set `f : (h.toLinearMap.toAddMonoidHom.comp P).range → P.range` to `fun z => ⟨h.symm z.1, by`.

Take `⟨x, hx⟩` from `z.2`. Conclude with `⟨x, by rw [← hx, ev, h.symm_apply_apply]⟩⟩`. Establish `hc : Continuous f` using `Continuous.subtype_mk (h.symm.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val) _`. Establish `hi : Function.Injective f` using `fun a b e => Subtype.ext (h.symm.injective (congrArg Subtype.val e))`. Conclude with `DiscreteTopology.of_continuous_injective hc hi`.

Establish `e : Set.range (h.toLinearMap.toAddMonoidHom.comp P) = (h.toLinearMap.restrictScalars ℝ) '' Set.range P`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[e, ← Submodule.map_span, h4, Submodule.map_top, LinearMap.range_eq_top]`. Conclude with `h.surjective`.

Establish `e1 : (B.map star)ᴴ = Bᵀ`. Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply]`. Establish `e2 : (Bᵀ)ᴴ = B.map star`. Use extensionality with `i j`.

Simplify using `[Matrix.conjTranspose_apply]`. Unfold `Matrix.IsHermitian`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, e1, e2, h5.eq, Matrix.mul_assoc]`. Rewrite using `[hermForm_pullback_matrix, hBv]`. Conclude with `h6 _ (fun e => hz (h.symm.map_eq_zero_iff.mp e))`.

Rewrite using `[hermForm_pullback_matrix, hBv, hBv, ev, ev, h.symm_apply_apply, h.symm_apply_apply, h7]`.
-/
theorem IsPeriod.comp_linearEquiv (O : Type) [Ring O] (bar : O → O) (D : PLat O bar) (g : ℕ)
    (ρ ρ₂ : O →+* Matrix (Fin g) (Fin g) ℂ) (P : D.La →+ (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hP : GlobalTheory.PELU.IsPeriod D ρ P) (hh : ∀ a z, h (ρ a *ᵥ z) = ρ₂ a *ᵥ h z) :
    GlobalTheory.PELU.IsPeriod D ρ₂ (h.toLinearMap.toAddMonoidHom.comp P) := by
  obtain ⟨h1, h2, h3, h4, Hm, h5, h6, h7⟩ := hP
  have ev : ∀ x, (h.toLinearMap.toAddMonoidHom.comp P) x = h (P x) := fun _ => rfl
  set B : Matrix (Fin g) (Fin g) ℂ := LinearMap.toMatrix' h.symm.toLinearMap with hB
  have hBv : ∀ u, B *ᵥ u = h.symm u := fun u => by
    rw [hB, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl
  refine ⟨fun a x => ?_, ?_, ?_, ?_, Bᵀ * Hm * B.map star, ?_, fun z hz => ?_, fun x y => ?_⟩
  · rw [ev, ev, h1, hh]
  · exact h.injective.comp h2
  · let f : (h.toLinearMap.toAddMonoidHom.comp P).range → P.range := fun z =>
      ⟨h.symm z.1, by
        obtain ⟨x, hx⟩ := z.2
        exact ⟨x, by rw [← hx, ev, h.symm_apply_apply]⟩⟩
    have hc : Continuous f :=
      Continuous.subtype_mk (h.symm.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val) _
    have hi : Function.Injective f := fun a b e => Subtype.ext (h.symm.injective (congrArg Subtype.val e))
    exact DiscreteTopology.of_continuous_injective hc hi
  · have e : Set.range (h.toLinearMap.toAddMonoidHom.comp P) = (h.toLinearMap.restrictScalars ℝ) '' Set.range P := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, h4, Submodule.map_top, LinearMap.range_eq_top]
    exact h.surjective
  · have e1 : (B.map star)ᴴ = Bᵀ := by
      ext i j; simp [Matrix.conjTranspose_apply]
    have e2 : (Bᵀ)ᴴ = B.map star := by
      ext i j; simp [Matrix.conjTranspose_apply]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, e1, e2, h5.eq, Matrix.mul_assoc]
  · rw [hermForm_pullback_matrix, hBv]
    exact h6 _ (fun e => hz (h.symm.map_eq_zero_iff.mp e))
  · rw [hermForm_pullback_matrix, hBv, hBv, ev, ev, h.symm_apply_apply, h.symm_apply_apply, h7]

end GlobalTheory.PELU
