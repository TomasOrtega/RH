import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescCocycle
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem finiteFlatSurj_affine_algebra : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y] (V₀ : Y.Opens), IsAffineOpen V₀ →
    letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
    IsNoetherianRing Γ(Y, V₀) ∧ Module.Finite Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) ∧ Module.FaithfullyFlat Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := by
  intro X Y f _ _ _ _ V₀ hV₀
  letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
  have hV : IsAffineOpen (f ⁻¹ᵁ V₀) := hV₀.preimage f
  refine ⟨IsLocallyNoetherian.component_noetherian ⟨V₀, hV₀⟩, ?_, ?_⟩
  · exact IsFinite.finite_app f V₀ hV₀
  · have hflat : (f.app V₀).hom.Flat := by
      have := Flat.flat_appLE f hV₀ hV le_rfl
      rwa [Scheme.Hom.appLE_eq_app] at this
    haveI : Module.Flat Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := hflat
    apply Module.FaithfullyFlat.of_comap_surjective
    intro p
    have hsq := IsAffineOpen.SpecMap_appLE_fromSpec f hV₀ hV le_rfl
    rw [Scheme.Hom.appLE_eq_app] at hsq
    have hy : hV₀.fromSpec p ∈ (V₀ : Set Y) := by
      rw [← hV₀.range_fromSpec]; exact ⟨p, rfl⟩
    obtain ⟨x, hx⟩ := f.surjective (hV₀.fromSpec p)
    have hxV : x ∈ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec]
      show f x ∈ (V₀ : Set Y)
      rw [hx]; exact hy
    obtain ⟨q, rfl⟩ := hxV
    refine ⟨q, ?_⟩
    apply hV₀.fromSpec.isOpenEmbedding.injective
    have := congrArg (fun g => g q) (congrArg (fun h => h.base) hsq)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    rw [← hx]
    convert this using 2
    rw [Spec.map_base]
    rfl

end GlobalTheory
