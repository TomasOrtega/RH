import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapCompSpMap
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
open GlobalTheory.HorComp

namespace GlobalTheory

/- English proof (translation)
Introduce `X _ _ S hS`. Take `⟨F, hF, hc, hi, hU⟩` from `NoetherianSpace.exists_finite_set_isClosed_irreducible hS`. Establish `key : ∀ W : Set X, _root_.IsIrreducible W → W ⊆ S → ∃ t ∈ F, W ⊆ t`. Introduce `W hW hWS`. Take `⟨t, ht, hWt⟩` from `isIrreducible_iff_sUnion_isClosed.1 hW hF.toFinset (fun z hz => hc z (hF.mem_toFinset.1 hz)) (by rw [hF.coe_toFinset, ← hU]; exact hWS)`.

Conclude with `⟨t, hF.mem_toFinset.1 ht, hWt⟩`. Establish `hsub : ∀ t ∈ F, t ⊆ S` using `fun t ht => by`. Rewrite using `[hU]`. Conclude with `Set.subset_sUnion_of_mem ht`. Use `⟨hF.subset ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `W hW`. Rewrite `hW` using `[Set.mem_setOf_eq]`. Take `⟨t, ht, hWt⟩` from `key W hW.prop.1 hW.prop.2`. Establish `h : t ⊆ W` using `hW.le_of_ge ⟨hi t ht, hsub t ht⟩ hWt`. Establish `: W = t` using `Set.Subset.antisymm hWt h`.

Rewrite using `[this]`. Conclude with `ht`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Conclude with `Set.sUnion_subset fun W hW => hW.1.2`. Introduce `x hx`.

Establish `hx' : x ∈ ⋃₀ F` using `hU ▸ hx`. Take `⟨t, ht, hxt⟩` from `hx'`. Take `⟨m, htm, hm⟩` from `hF.exists_le_maximal ht`. Use `⟨m, ⟨⟨hi m hm.prop, hsub m hm.prop⟩, ?_⟩, htm hxt⟩` and prove the remaining obligations. Introduce `W hW hmW`.

Take `⟨t', ht', hWt'⟩` from `key W hW.1 hW.2`. Conclude with `le_trans hWt' (hm.le_of_ge ht' (le_trans hmW hWt'))`. Introduce `W hW`. Establish `h : closure W ⊆ W` using `hW.le_of_ge ⟨hW.prop.1.closure, closure_minimal hW.prop.2 hS⟩ subset_closure`. Conclude with `closure_subset_iff_isClosed.1 h`.
-/
theorem closed_eq_sUnion_maximal_irreducible :
    ∀ (X : Type) [TopologicalSpace X] [NoetherianSpace X] (S : Set X), IsClosed S → {W : Set X | Maximal (fun W : Set X => _root_.IsIrreducible W ∧ W ⊆ S) W}.Finite ∧ ⋃₀ {W : Set X | Maximal (fun W : Set X => _root_.IsIrreducible W ∧ W ⊆ S) W} = S ∧ ∀ W : Set X, Maximal (fun W : Set X => _root_.IsIrreducible W ∧ W ⊆ S) W → IsClosed W := by
  intro X _ _ S hS
  obtain ⟨F, hF, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  have key : ∀ W : Set X, _root_.IsIrreducible W → W ⊆ S → ∃ t ∈ F, W ⊆ t := by
    intro W hW hWS
    obtain ⟨t, ht, hWt⟩ := isIrreducible_iff_sUnion_isClosed.1 hW hF.toFinset
      (fun z hz => hc z (hF.mem_toFinset.1 hz)) (by rw [hF.coe_toFinset, ← hU]; exact hWS)
    exact ⟨t, hF.mem_toFinset.1 ht, hWt⟩
  have hsub : ∀ t ∈ F, t ⊆ S := fun t ht => by
    rw [hU]; exact Set.subset_sUnion_of_mem ht
  refine ⟨hF.subset ?_, ?_, ?_⟩
  · intro W hW
    rw [Set.mem_setOf_eq] at hW
    obtain ⟨t, ht, hWt⟩ := key W hW.prop.1 hW.prop.2
    have h : t ⊆ W := hW.le_of_ge ⟨hi t ht, hsub t ht⟩ hWt
    have : W = t := Set.Subset.antisymm hWt h
    rw [this]; exact ht
  · apply Set.Subset.antisymm
    · exact Set.sUnion_subset fun W hW => hW.1.2
    · intro x hx
      have hx' : x ∈ ⋃₀ F := hU ▸ hx
      obtain ⟨t, ht, hxt⟩ := hx'
      obtain ⟨m, htm, hm⟩ := hF.exists_le_maximal ht
      refine ⟨m, ⟨⟨hi m hm.prop, hsub m hm.prop⟩, ?_⟩, htm hxt⟩
      intro W hW hmW
      obtain ⟨t', ht', hWt'⟩ := key W hW.1 hW.2
      exact le_trans hWt' (hm.le_of_ge ht' (le_trans hmW hWt'))
  · intro W hW
    have h : closure W ⊆ W := hW.le_of_ge
      ⟨hW.prop.1.closure, closure_minimal hW.prop.2 hS⟩ subset_closure
    exact closure_subset_iff_isClosed.1 h

end GlobalTheory
