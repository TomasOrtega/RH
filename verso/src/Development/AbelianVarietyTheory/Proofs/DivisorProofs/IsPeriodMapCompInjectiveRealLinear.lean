import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

namespace GlobalTheory.PELU

/- English proof (translation)
Take `⟨h1, h2, h3, h4, -⟩` from `hP₀`. Establish `hsurj : Function.Surjective R` using `LinearMap.injective_iff_surjective.mp hR`. Set `e : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ)` to `LinearEquiv.ofInjectiveEndo R hR`. Establish `he : ∀ z, e z = R z` using `fun z => rfl`. Set `ec` to `e.toContinuousLinearEquiv`.

Use `⟨?_, ?_, ?_, ?_, M, hM, hpos, ?_⟩` and prove the remaining obligations. Introduce `a x`. Simplify using `only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, h1, hRρ]`. Conclude with `hR.comp h2`. Set `f : (R.toAddMonoidHom.comp P₀).range → P₀.range` to `fun z => ⟨ec.symm z.1, by`.

Take `⟨z, x, rfl⟩` from `z`. Conclude with `⟨x, (e.symm_apply_apply (P₀ x)).symm⟩⟩`. Establish `hf : Continuous f`. Apply `Continuous.subtype_mk` to reduce the goal to its premises. Conclude with `ec.symm.continuous.comp continuous_subtype_val`.

Establish `hi : Function.Injective f`. Introduce `z w h`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg (fun u : P₀.range => ec u.1) h` as an intermediate fact. Simplify `this` using `[f]`.

Conclude with `DiscreteTopology.of_continuous_injective hf hi`. Establish `: Set.range (R.toAddMonoidHom.comp P₀) = R '' Set.range P₀`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[this, Submodule.span_image, h4, Submodule.map_top, LinearMap.range_eq_top]`.

Conclude with `hsurj`. Introduce `x y`. Conclude with `hE x y`.
-/
theorem isPeriod_comp_realLinear {O : Type} [Ring O] {bar : O → O} (D : PLat O bar) {g : ℕ}
    (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (P₀ : D.La →+ (Fin g → ℂ)) (R : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (M : Matrix (Fin g) (Fin g) ℂ) (hP₀ : IsPeriod D ρ P₀) (hR : Function.Injective R)
    (hRρ : ∀ (a : O) x, R (ρ a *ᵥ P₀ x) = ρ a *ᵥ R (P₀ x)) (hM : M.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re)
    (hE : ∀ x y, (hermForm M (R (P₀ x)) (R (P₀ y))).im = D.EF x y) :
    IsPeriod D ρ (R.toAddMonoidHom.comp P₀) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hP₀
  have hsurj : Function.Surjective R := LinearMap.injective_iff_surjective.mp hR
  let e : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := LinearEquiv.ofInjectiveEndo R hR
  have he : ∀ z, e z = R z := fun z => rfl
  let ec := e.toContinuousLinearEquiv
  refine ⟨?_, ?_, ?_, ?_, M, hM, hpos, ?_⟩
  · intro a x
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, h1, hRρ]
  · exact hR.comp h2
  · let f : (R.toAddMonoidHom.comp P₀).range → P₀.range := fun z =>
      ⟨ec.symm z.1, by
        obtain ⟨z, x, rfl⟩ := z
        exact ⟨x, (e.symm_apply_apply (P₀ x)).symm⟩⟩
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      exact ec.symm.continuous.comp continuous_subtype_val
    have hi : Function.Injective f := by
      intro z w h
      apply Subtype.ext
      have := congrArg (fun u : P₀.range => ec u.1) h
      simpa [f] using this
    exact DiscreteTopology.of_continuous_injective hf hi
  · have : Set.range (R.toAddMonoidHom.comp P₀) = R '' Set.range P₀ := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, h4, Submodule.map_top, LinearMap.range_eq_top]
    exact hsurj
  · intro x y
    exact hE x y

end GlobalTheory.PELU
