import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnOfHoloOn
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
open GlobalTheory.IrrAn

namespace GlobalTheory.IrrAn

open ReciprocityTheory.AnForm.M

/- English proof (translation)
Introduce `d Y _ A S Z₁ Z₂ hS _ hL hA1 hA2 hsub`. Distinguish the cases in `h1 : S ⊆ Z₁`. Conclude with `Or.inl h1`. Use `right`. Take `⟨x0, hx0S, hx0Z⟩` from `Set.not_subset.1 h1`.

Establish `hZ1c : IsClosed Z₁` using `GlobalTheory.IrrAn.isClosed_of_isAnalyticSubset A hA1`. Set `G : Set Y` to `{x | ∀ᶠ y in 𝓝 x, y ∈ S → y ∈ Z₂}`. Establish `hGo : IsOpen G`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x hx`.

Conclude with `Filter.Eventually.eventually_nhds hx`. Establish `hGcl : ∀ x ∈ S, x ∈ closure (S ∩ G) → x ∈ G`. Introduce `x hxS hx`. Take `⟨W, hW, hxW, r, f, hf, hZW⟩` from `hA2 x`. Take `⟨N, hN, hxN, hNW, hNid⟩` from `hL x hxS W hW hxW`.

Take `⟨x', hx'N, hx'S, hx'G⟩` from `mem_closure_iff.1 hx N hN hxN`. Establish `hvan : ∀ i, ∀ y ∈ S ∩ N, f i y = 0`. Introduce `i`. Use `hNid (f i) (hf i) x' ⟨hx'S, hx'N⟩ ?_` and prove the remaining obligations. Use `filter_upwards [hx'G, hN.mem_nhds hx'N] with y hy hyN hyS`.

Establish `hyZW : y ∈ Z₂ ∩ W` using `⟨hy hyS, hNW hyN⟩`. Rewrite `hyZW` using `[hZW]`. Conclude with `hyZW.2 i`. Use `show ∀ᶠ y in 𝓝 x, y ∈ S → y ∈ Z₂`. Use `filter_upwards [hN.mem_nhds hxN] with y hyN hyS`.

Establish `hy : y ∈ {y ∈ W | ∀ i, f i y = 0}` using `⟨hNW hyN, fun i => hvan i y ⟨hyS, hyN⟩⟩`. Rewrite `hy` using `[← hZW]`. Conclude with `hy.1`. Establish `hx0G : x0 ∈ G` using `by show ∀ᶠ y in 𝓝 x0, y ∈ S → y ∈ Z₂ filter_upwards [hZ1c.isOpen_compl.mem_nhds hx0Z] with y hy hyS`. Conclude with `(hsub hyS).resolve_left hy`.

Establish `hSG : S ⊆ G` using `by haveI := Subtype.preconnectedSpace hS`. Set `T : Set S` to `Subtype.val ⁻¹' G`. Establish `hTc : IsClopen T`. Use `⟨?_, hGo.preimage continuous_subtype_val⟩` and prove the remaining obligations. Use `isClosed_of_closure_subset fun x hx => ?_` and prove the remaining obligations.

Rewrite `hx` using `[closure_subtype]`. Apply `hGcl x x.2` to reduce the goal to its premises. Use `closure_mono ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `⟨y.2, hy⟩`.

Break down `isClopen_iff.1 hTc with h | h` into its components or cases. Establish `hm : (⟨x0, hx0S⟩ : S) ∈ T` using `hx0G`. Rewrite `hm` using `[h]`. Conclude with `absurd hm (Set.notMem_empty _)`. Introduce `x hx`.

Establish `hm : (⟨x, hx⟩ : S) ∈ T` using `by rw [h]; trivial`. Conclude with `hm`. Introduce `x hx`. Conclude with `Filter.Eventually.self_of_nhds (hSG hx) hx`.
-/
theorem subset_or_subset_of_locIdent : ∀ (d : ℕ) (Y : Type) [TopologicalSpace Y] (A : FinHolAtlas d Y) (S Z₁ Z₂ : Set Y), IsPreconnected S → S.Nonempty → GlobalTheory.IrrAn.LocIdent A S → A.IsAnalyticSubset Z₁ → A.IsAnalyticSubset Z₂ → S ⊆ Z₁ ∪ Z₂ → S ⊆ Z₁ ∨ S ⊆ Z₂ := by
  intro d Y _ A S Z₁ Z₂ hS _ hL hA1 hA2 hsub
  by_cases h1 : S ⊆ Z₁
  · exact Or.inl h1
  right
  obtain ⟨x0, hx0S, hx0Z⟩ := Set.not_subset.1 h1
  have hZ1c : IsClosed Z₁ := GlobalTheory.IrrAn.isClosed_of_isAnalyticSubset A hA1
  let G : Set Y := {x | ∀ᶠ y in 𝓝 x, y ∈ S → y ∈ Z₂}
  have hGo : IsOpen G := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact Filter.Eventually.eventually_nhds hx
  have hGcl : ∀ x ∈ S, x ∈ closure (S ∩ G) → x ∈ G := by
    intro x hxS hx
    obtain ⟨W, hW, hxW, r, f, hf, hZW⟩ := hA2 x
    obtain ⟨N, hN, hxN, hNW, hNid⟩ := hL x hxS W hW hxW
    obtain ⟨x', hx'N, hx'S, hx'G⟩ := mem_closure_iff.1 hx N hN hxN
    have hvan : ∀ i, ∀ y ∈ S ∩ N, f i y = 0 := by
      intro i
      refine hNid (f i) (hf i) x' ⟨hx'S, hx'N⟩ ?_
      filter_upwards [hx'G, hN.mem_nhds hx'N] with y hy hyN hyS
      have hyZW : y ∈ Z₂ ∩ W := ⟨hy hyS, hNW hyN⟩
      rw [hZW] at hyZW
      exact hyZW.2 i
    show ∀ᶠ y in 𝓝 x, y ∈ S → y ∈ Z₂
    filter_upwards [hN.mem_nhds hxN] with y hyN hyS
    have hy : y ∈ {y ∈ W | ∀ i, f i y = 0} := ⟨hNW hyN, fun i => hvan i y ⟨hyS, hyN⟩⟩
    rw [← hZW] at hy
    exact hy.1
  have hx0G : x0 ∈ G := by
    show ∀ᶠ y in 𝓝 x0, y ∈ S → y ∈ Z₂
    filter_upwards [hZ1c.isOpen_compl.mem_nhds hx0Z] with y hy hyS
    exact (hsub hyS).resolve_left hy
  have hSG : S ⊆ G := by
    haveI := Subtype.preconnectedSpace hS
    let T : Set S := Subtype.val ⁻¹' G
    have hTc : IsClopen T := by
      refine ⟨?_, hGo.preimage continuous_subtype_val⟩
      refine isClosed_of_closure_subset fun x hx => ?_
      rw [closure_subtype] at hx
      apply hGcl x x.2
      refine closure_mono ?_ hx
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    rcases isClopen_iff.1 hTc with h | h
    · have hm : (⟨x0, hx0S⟩ : S) ∈ T := hx0G
      rw [h] at hm
      exact absurd hm (Set.notMem_empty _)
    · intro x hx
      have hm : (⟨x, hx⟩ : S) ∈ T := by rw [h]; trivial
      exact hm
  intro x hx
  exact Filter.Eventually.self_of_nhds (hSG hx) hx

end GlobalTheory.IrrAn
