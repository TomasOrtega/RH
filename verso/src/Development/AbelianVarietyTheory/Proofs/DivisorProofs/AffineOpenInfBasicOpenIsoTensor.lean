import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ T π B _ _ U₁ e₁ h r`. Use `letI : Algebra B (Localization.Away r ⊗[R] B) := Algebra.TensorProduct.rightAlgebra`. Use `haveI : IsLocalization.Away (algebraMap R B r) (Localization.Away r ⊗[R] B) := by`. Use `IsLocalization.tensorRight (R := R) (S := B) (Localization.Away r) (Submonoid.powers r)` as an intermediate fact. Simplify `this` using `[Algebra.algebraMapSubmonoid, Submonoid.map_powers]`.

Set `g : Sp (Localization.Away r ⊗[R] B) ⟶ Sp B` to `spMap (algebraMap B (Localization.Away r ⊗[R] B))`. Use `haveI : IsOpenImmersion g := IsOpenImmersion.of_isLocalization (algebraMap R B r)`. Set `f : Sp (Localization.Away r ⊗[R] B) ⟶ T` to `g ≫ e₁.hom ≫ U₁.ι`. Establish `hg : Set.range g.base = (PrimeSpectrum.basicOpen (algebraMap R B r) : Set (PrimeSpectrum B))` using `PrimeSpectrum.localization_away_comap_range _ _`. Establish `hr : Set.range f.base = Set.range (U₁ ⊓ π ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Sp R).Opens)).ι.base`.

Rewrite using `[Scheme.Opens.range_ι]`. Establish `key : ∀ y : Sp B, π (U₁.ι (e₁.hom y)) ∈ (PrimeSpectrum.basicOpen r : (Sp R).Opens) ↔ y ∈ Set.range g.base`. Introduce `y`. Rewrite using `[hg, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]`. Both sides reduce to the same expression.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Use `⟨(e₁.hom (g z)).2, ?_⟩` and prove the remaining obligations. Conclude with `(key (g z)).2 ⟨z, rfl⟩`.

Introduce and unpack `⟨hx, hx'⟩`. Take `⟨y, hy⟩` from `e₁.hom.surjective ⟨x, hx⟩`. Establish `hy' : U₁.ι (e₁.hom y) = x` using `by rw [hy]; rfl`. Take `⟨z, hz⟩` from `(key y).1 (by rw [hy']; exact hx')`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hy', ← hz]`. Both sides reduce to the same expression. Use `⟨IsOpenImmersion.isoOfRangeEq f _ hr, ?_⟩` and prove the remaining obligations. Rewrite using `[IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]`. Simplify using `only [f, Category.assoc, h, g]`.

Rewrite using `[spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Conclude with `(Algebra.TensorProduct.includeRight (R := R) (A := Localization.Away r) (B := B)).comp_algebraMap`.
-/
theorem affineOpen_inf_basicOpen_iso_tensor :
    ∀ (R : Type) [CommRing R] (T : Scheme.{0}) (π : T ⟶ Sp R) (B : Type) [CommRing B] [Algebra R B] (U₁ : T.Opens) (e₁ : Sp B ≅ U₁.toScheme), e₁.hom ≫ U₁.ι ≫ π = spMap (algebraMap R B) → ∀ r : R, ∃ e : Sp (Localization.Away r ⊗[R] B) ≅ (U₁ ⊓ π ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Sp R).Opens)).toScheme, e.hom ≫ (U₁ ⊓ π ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Sp R).Opens)).ι ≫ π = spMap (algebraMap R (Localization.Away r ⊗[R] B)) := by
  intro R _ T π B _ _ U₁ e₁ h r
  letI : Algebra B (Localization.Away r ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization.Away (algebraMap R B r) (Localization.Away r ⊗[R] B) := by
    have := IsLocalization.tensorRight (R := R) (S := B) (Localization.Away r) (Submonoid.powers r)
    simpa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using this
  let g : Sp (Localization.Away r ⊗[R] B) ⟶ Sp B := spMap (algebraMap B (Localization.Away r ⊗[R] B))
  haveI : IsOpenImmersion g := IsOpenImmersion.of_isLocalization (algebraMap R B r)
  let f : Sp (Localization.Away r ⊗[R] B) ⟶ T := g ≫ e₁.hom ≫ U₁.ι
  have hg : Set.range g.base = (PrimeSpectrum.basicOpen (algebraMap R B r) : Set (PrimeSpectrum B)) :=
    PrimeSpectrum.localization_away_comap_range _ _
  have hr : Set.range f.base = Set.range (U₁ ⊓ π ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Sp R).Opens)).ι.base := by
    rw [Scheme.Opens.range_ι]
    have key : ∀ y : Sp B, π (U₁.ι (e₁.hom y)) ∈ (PrimeSpectrum.basicOpen r : (Sp R).Opens) ↔
        y ∈ Set.range g.base := by
      intro y
      rw [hg, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]
      rfl
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨(e₁.hom (g z)).2, ?_⟩
      exact (key (g z)).2 ⟨z, rfl⟩
    · rintro ⟨hx, hx'⟩
      obtain ⟨y, hy⟩ := e₁.hom.surjective ⟨x, hx⟩
      have hy' : U₁.ι (e₁.hom y) = x := by rw [hy]; rfl
      obtain ⟨z, hz⟩ := (key y).1 (by rw [hy']; exact hx')
      refine ⟨z, ?_⟩
      rw [← hy', ← hz]; rfl
  refine ⟨IsOpenImmersion.isoOfRangeEq f _ hr, ?_⟩
  rw [IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
  simp only [f, Category.assoc, h, g]
  rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (Algebra.TensorProduct.includeRight (R := R) (A := Localization.Away r) (B := B)).comp_algebraMap

end GlobalTheory
