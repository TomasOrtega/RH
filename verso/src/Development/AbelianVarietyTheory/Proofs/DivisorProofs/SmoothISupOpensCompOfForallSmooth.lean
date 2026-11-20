import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

/- English proof (translation)
Establish `hloc : IsZariskiLocalAtSource @Smooth.{0}` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Use `set U := ⨆ i, V i with hUdef`. Establish `hle : ∀ i, V i ≤ U` using `fun i => le_iSup V i`. Use `IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth.{0}) (fun i => U.ι ⁻¹ᵁ V i) ?_ ?_` and prove the remaining obligations. Apply `top_unique` to reduce the goal to its premises.

Introduce `x _`. Establish `hx : (U.ι x : P') ∈ (⨆ i, V i : P'.Opens)` using `x.2`. Rewrite `hx` using `[TopologicalSpace.Opens.mem_iSup]`. Take `⟨i, hi⟩` from `hx`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩`.

Introduce `i`. Establish `hrange : Set.range ((U.ι ⁻¹ᵁ V i).ι ≫ U.ι) = Set.range (V i).ι`. Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]`. Use extensionality with `y`. Simplify using `only [Set.mem_image, SetLike.mem_coe, Scheme.Hom.mem_preimage]`.

Conclude with `⟨by rintro ⟨x, hx, rfl⟩; exact hx, fun hy => ⟨⟨y, hle i hy⟩, hy, rfl⟩⟩`. Rewrite using `[← Category.assoc, ← IsOpenImmersion.isoOfRangeEq_hom_fac ((U.ι ⁻¹ᵁ V i).ι ≫ U.ι) (V i).ι hrange, Category.assoc]`. Use `haveI := h i`. Use `infer_instance`.
-/
theorem GlobalTheory.Mum.smooth_iSup_comp (P' T : Scheme.{0}) (q : P' ⟶ T) (I : Type) (V : I → P'.Opens)
    (h : ∀ i, Smooth ((V i).ι ≫ q)) : Smooth ((⨆ i, V i).ι ≫ q) := by
  have hloc : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  set U := ⨆ i, V i with hUdef
  have hle : ∀ i, V i ≤ U := fun i => le_iSup V i
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth.{0}) (fun i => U.ι ⁻¹ᵁ V i) ?_ ?_
  · apply top_unique
    intro x _
    have hx : (U.ι x : P') ∈ (⨆ i, V i : P'.Opens) := x.2
    rw [TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨i, hi⟩ := hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    have hrange : Set.range ((U.ι ⁻¹ᵁ V i).ι ≫ U.ι) = Set.range (V i).ι := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
        Scheme.Opens.range_ι]
      ext y
      simp only [Set.mem_image, SetLike.mem_coe, Scheme.Hom.mem_preimage]
      exact ⟨by rintro ⟨x, hx, rfl⟩; exact hx, fun hy => ⟨⟨y, hle i hy⟩, hy, rfl⟩⟩
    rw [← Category.assoc, ← IsOpenImmersion.isoOfRangeEq_hom_fac ((U.ι ⁻¹ᵁ V i).ι ≫ U.ι) (V i).ι hrange,
      Category.assoc]
    haveI := h i
    infer_instance
