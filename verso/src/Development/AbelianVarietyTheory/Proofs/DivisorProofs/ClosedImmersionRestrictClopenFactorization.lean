import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Introduce `X Z₁ i hi U hU`. Establish `hVc : IsClosed (Set.range (i ⁻¹ᵁ U).ι.base)`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hU.preimage i.base.hom.continuous`. Use `haveI : IsClosedImmersion (i ⁻¹ᵁ U).ι := IsClosedImmersion.of_isPreimmersion _ hVc`.

Use `⟨(i ⁻¹ᵁ U), (i ⁻¹ᵁ U).ι ≫ i, inferInstance, fun T g => ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Use `⟨⟨z ≫ (i ⁻¹ᵁ U).ι, by simp⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨t, rfl⟩`.

Establish `: ((i ⁻¹ᵁ U).ι.base (z.base t)) ∈ (i ⁻¹ᵁ U : Set Z₁)`. Rewrite using `[← Scheme.Opens.range_ι]`. Conclude with `⟨_, rfl⟩`. Simplify `this` using `[Scheme.Hom.comp_base]`. Introduce and unpack `⟨⟨y, rfl⟩, hg⟩`.

Establish `h : Set.range y.base ⊆ Set.range (i ⁻¹ᵁ U).ι.base`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨t, rfl⟩`. Use `hg ⟨t, rfl⟩` as an intermediate fact. Simplify using `using this`.

Conclude with `⟨IsOpenImmersion.lift (i ⁻¹ᵁ U).ι y h, by rw [← Category.assoc, IsOpenImmersion.lift_fac]⟩`.
-/
theorem clopen_cut_closedImmersion : ∀ {X Z₁ : Scheme.{0}} (i : Z₁ ⟶ X), IsClosedImmersion i → ∀ (U : X.Opens), IsClosed (U : Set X) → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), ((∃ z : T ⟶ Z, z ≫ j = g) ↔ (∃ y : T ⟶ Z₁, y ≫ i = g) ∧ Set.range g.base ⊆ (U : Set X)) := by
  intro X Z₁ i hi U hU
  have hVc : IsClosed (Set.range (i ⁻¹ᵁ U).ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact hU.preimage i.base.hom.continuous
  haveI : IsClosedImmersion (i ⁻¹ᵁ U).ι := IsClosedImmersion.of_isPreimmersion _ hVc
  refine ⟨(i ⁻¹ᵁ U), (i ⁻¹ᵁ U).ι ≫ i, inferInstance, fun T g => ?_⟩
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z ≫ (i ⁻¹ᵁ U).ι, by simp⟩, ?_⟩
    rintro _ ⟨t, rfl⟩
    have : ((i ⁻¹ᵁ U).ι.base (z.base t)) ∈ (i ⁻¹ᵁ U : Set Z₁) := by
      rw [← Scheme.Opens.range_ι]; exact ⟨_, rfl⟩
    simpa [Scheme.Hom.comp_base] using this
  · rintro ⟨⟨y, rfl⟩, hg⟩
    have h : Set.range y.base ⊆ Set.range (i ⁻¹ᵁ U).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      have := hg ⟨t, rfl⟩
      simpa using this
    exact ⟨IsOpenImmersion.lift (i ⁻¹ᵁ U).ι y h, by rw [← Category.assoc, IsOpenImmersion.lift_fac]⟩

end GlobalTheory
