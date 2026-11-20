import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
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
