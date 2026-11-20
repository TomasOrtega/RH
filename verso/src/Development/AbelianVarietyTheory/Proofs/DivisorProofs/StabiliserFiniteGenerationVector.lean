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
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Prove the first alternative. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
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
