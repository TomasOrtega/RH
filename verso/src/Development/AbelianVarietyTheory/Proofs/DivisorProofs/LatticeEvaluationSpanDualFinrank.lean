import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

/- English proof (translation)
Introduce `W _ _ Λ _ n b P hinj hsurj`. Set `Φ : W →ₗ[ℂ] (Fin n → ℂ)` to `LinearMap.pi (fun i => P (b i))`. Establish `hΦ : ∀ w i, Φ w i = P (b i) w` using `fun w i => rfl`. Establish `h1 : Function.Injective Φ`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `w hw`. Apply `hinj` to reduce the goal to its premises. Introduce `l`. Rewrite using `[← b.sum_repr l, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_zsmul, LinearMap.smul_apply, ← hΦ, hw]`. Simplify using the standard rewrite rules. Establish `h2 : Function.Surjective Φ`. Introduce `v`. Take `⟨w, hw⟩` from `hsurj (b.constr ℤ v).toAddMonoidHom`.

Use `⟨w, funext fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hΦ, hw]`. Simplify using the standard rewrite rules. Set `e : W ≃ₗ[ℂ] (Fin n → ℂ)` to `LinearEquiv.ofBijective Φ ⟨h1, h2⟩`. Set `c : Module.Basis (Fin n) ℂ W` to `Module.Basis.ofEquivFun e`.

Establish `hc : ∀ i, c.dualBasis i = P (b i)`. Introduce `i`. Use extensionality with `w`. Rewrite using `[Module.Basis.dualBasis_apply]`. Conclude with `hΦ w i`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← c.dualBasis.span_eq]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨b i, (hc i).symm⟩`.

Simplify using `using Module.finrank_eq_card_basis c.dualBasis`.
-/
theorem span_eval_eq_top_and_finrank_dual : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (Λ : Type) [AddCommGroup Λ] (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ) (P : Λ →+ Module.Dual ℂ W), (∀ w, (∀ l, P l w = 0) → w = 0) → (∀ p : Λ →+ ℂ, ∃ w, ∀ l, P l w = p l) → Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (Module.Dual ℂ W) = n := by
  intro W _ _ Λ _ n b P hinj hsurj
  let Φ : W →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i => P (b i))
  have hΦ : ∀ w i, Φ w i = P (b i) w := fun w i => rfl
  have h1 : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    apply hinj
    intro l
    rw [← b.sum_repr l, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_zsmul, LinearMap.smul_apply, ← hΦ, hw]
    simp
  have h2 : Function.Surjective Φ := by
    intro v
    obtain ⟨w, hw⟩ := hsurj (b.constr ℤ v).toAddMonoidHom
    refine ⟨w, funext fun i => ?_⟩
    rw [hΦ, hw]
    simp
  let e : W ≃ₗ[ℂ] (Fin n → ℂ) := LinearEquiv.ofBijective Φ ⟨h1, h2⟩
  let c : Module.Basis (Fin n) ℂ W := Module.Basis.ofEquivFun e
  have hc : ∀ i, c.dualBasis i = P (b i) := by
    intro i
    ext w
    rw [Module.Basis.dualBasis_apply]
    exact hΦ w i
  refine ⟨?_, ?_⟩
  · rw [eq_top_iff, ← c.dualBasis.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, (hc i).symm⟩
  · simpa using Module.finrank_eq_card_basis c.dualBasis

end GlobalTheory.CechPer
