import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualRevDualRev
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FnExt

/- English proof (translation)
Introduce `O _ _ _ Ω _ _ K J y hy O' _ _ _ _ Ω' _ _ _ _ _ _ ζ hζ`. Use `set L := fnField O' (fun v => algebraMap Ω Ω' (y v)) with hL`. Establish `himg : ∀ a : Ω, algebraMap Ω Ω' a ∈ L`. Establish `hmap : (⊤ : Subfield Ω).map (algebraMap Ω Ω') ≤ L`. Rewrite using `[← hy]`.

Unfold `fnField`. Rewrite using `[Subfield.map_le_iff_le_comap, Subfield.closure_le]`. Introduce and unpack `x (⟨a, rfl⟩ | ⟨q, rfl⟩)`. Use `show algebraMap Ω Ω' (algebraMap O Ω a) ∈ L`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply O O' Ω']`.

Conclude with `Subfield.subset_closure (Or.inl ⟨_, rfl⟩)`. Use `show algebraMap Ω Ω' (y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩) ∈ L`. Rewrite using `[map_div₀]`. Conclude with `Subfield.subset_closure (Or.inr ⟨q, rfl⟩)`. Introduce `a`.

Conclude with `hmap ⟨a, Subfield.mem_top a, rfl⟩`. Establish `hζL : algebraMap O' Ω' ζ ∈ L` using `Subfield.subset_closure (Or.inl ⟨ζ, rfl⟩)`. Set `S : Subalgebra Ω Ω'` to `{ L.toSubring with algebraMap_mem' := himg }`. Establish `hle : Algebra.adjoin Ω {algebraMap O' Ω' ζ} ≤ S`. Rewrite using `[Algebra.adjoin_le_iff]`.

Rewrite using `[Set.singleton_subset_iff]`. Conclude with `hζL`. Rewrite `hle` using `[hζ]`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Conclude with `hle (Algebra.mem_top (x := x))`.
-/
theorem fnField_top_of_adjoin_root : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω), fnField O y = ⊤ →
    ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (Ω' : Type) [Field Ω']
      [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'] (ζ : O'),
      Algebra.adjoin Ω {algebraMap O' Ω' ζ} = ⊤ → fnField O' (fun v => algebraMap Ω Ω' (y v)) = ⊤ := by
  intro O _ _ _ Ω _ _ K J y hy O' _ _ _ _ Ω' _ _ _ _ _ _ ζ hζ
  set L := fnField O' (fun v => algebraMap Ω Ω' (y v)) with hL

  have himg : ∀ a : Ω, algebraMap Ω Ω' a ∈ L := by
    have hmap : (⊤ : Subfield Ω).map (algebraMap Ω Ω') ≤ L := by
      rw [← hy]
      unfold fnField
      rw [Subfield.map_le_iff_le_comap, Subfield.closure_le]
      rintro x (⟨a, rfl⟩ | ⟨q, rfl⟩)
      · show algebraMap Ω Ω' (algebraMap O Ω a) ∈ L
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply O O' Ω']
        exact Subfield.subset_closure (Or.inl ⟨_, rfl⟩)
      · show algebraMap Ω Ω' (y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩) ∈ L
        rw [map_div₀]
        exact Subfield.subset_closure (Or.inr ⟨q, rfl⟩)
    intro a
    exact hmap ⟨a, Subfield.mem_top a, rfl⟩
  have hζL : algebraMap O' Ω' ζ ∈ L := Subfield.subset_closure (Or.inl ⟨ζ, rfl⟩)
  let S : Subalgebra Ω Ω' :=
    { L.toSubring with algebraMap_mem' := himg }
  have hle : Algebra.adjoin Ω {algebraMap O' Ω' ζ} ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rw [Set.singleton_subset_iff]
    exact hζL
  rw [hζ] at hle
  rw [eq_top_iff]
  intro x _
  exact hle (Algebra.mem_top (x := x))

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FnExt
