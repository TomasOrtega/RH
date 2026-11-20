import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TailCut

/- English proof (translation)
Introduce `ι _ a S S' hsum hSS'`. Establish `hmul : ∀ T : Set ι, Multipliable (T.mulIndicator a)`. Introduce `T`. Establish `hs : Summable fun v => ‖T.mulIndicator a v - 1‖`. Use `Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_) hsum` and prove the remaining obligations.

Distinguish the cases in `hv : v ∈ T`. Simplify using `[Set.mulIndicator_of_mem hv, Real.norm_eq_abs]`. Simplify using `[Set.mulIndicator_of_notMem hv]`. Establish `h` using `multipliable_one_add_of_summable hs`. Simplify using `using h`.

Establish `e1 : (∏' v : {v // v ∉ S}, a v.1) = ∏' v, Set.mulIndicator {v | v ∉ S} a v` using `tprod_subtype {v | v ∉ S} a`. Establish `e2 : (∏' v : {v // v ∉ S'}, a v.1) = ∏' v, Set.mulIndicator {v | v ∉ S'} a v` using `tprod_subtype {v | v ∉ S'} a`. Establish `hsplit : (∏' v, Set.mulIndicator {v | v ∉ S} a v) = ∏' v, (Set.mulIndicator (↑(S' \ S) : Set ι) a v * Set.mulIndicator {v | v ∉ S'} a v)`. Use `tprod_congr fun v => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : v ∈ S`.

Establish `h2 : v ∈ S'` using `hSS' h1`. Simplify using `[Set.mulIndicator, h1, h2]`. Distinguish the cases in `h2 : v ∈ S'`. Simplify using `[Set.mulIndicator, h1, h2]`. Simplify using `[Set.mulIndicator, h1, h2]`.

Establish `hfin : (∏' v, Set.mulIndicator (↑(S' \ S) : Set ι) a v) = ∏ v ∈ S' \ S, a v`. Rewrite using `[tprod_eq_prod (s := S' \ S)]`. Conclude with `Finset.prod_congr rfl fun v hv => Set.mulIndicator_of_mem (Finset.mem_coe.mpr hv) a`. Introduce `v hv`. Conclude with `Set.mulIndicator_of_notMem (by rwa [Finset.mem_coe]) a`.

Rewrite using `[e1, e2, hsplit, Multipliable.tprod_mul (hmul _) (hmul _), hfin]`.
-/
theorem tprod_tail_cut : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (S S' : Finset ι),
    Summable (fun v => |a v - 1|) → S ⊆ S' →
      ∏' v : {v // v ∉ S}, a v.1 = (∏ v ∈ S' \ S, a v) * ∏' v : {v // v ∉ S'}, a v.1 := by
  intro ι _ a S S' hsum hSS'
  have hmul : ∀ T : Set ι, Multipliable (T.mulIndicator a) := by
    intro T
    have hs : Summable fun v => ‖T.mulIndicator a v - 1‖ := by
      refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_) hsum
      by_cases hv : v ∈ T
      · simp [Set.mulIndicator_of_mem hv, Real.norm_eq_abs]
      · simp [Set.mulIndicator_of_notMem hv]
    have h := multipliable_one_add_of_summable hs
    simpa using h
  have e1 : (∏' v : {v // v ∉ S}, a v.1) = ∏' v, Set.mulIndicator {v | v ∉ S} a v :=
    tprod_subtype {v | v ∉ S} a
  have e2 : (∏' v : {v // v ∉ S'}, a v.1) = ∏' v, Set.mulIndicator {v | v ∉ S'} a v :=
    tprod_subtype {v | v ∉ S'} a
  have hsplit : (∏' v, Set.mulIndicator {v | v ∉ S} a v) =
      ∏' v, (Set.mulIndicator (↑(S' \ S) : Set ι) a v * Set.mulIndicator {v | v ∉ S'} a v) := by
    refine tprod_congr fun v => ?_
    by_cases h1 : v ∈ S
    · have h2 : v ∈ S' := hSS' h1
      simp [Set.mulIndicator, h1, h2]
    · by_cases h2 : v ∈ S'
      · simp [Set.mulIndicator, h1, h2]
      · simp [Set.mulIndicator, h1, h2]
  have hfin : (∏' v, Set.mulIndicator (↑(S' \ S) : Set ι) a v) = ∏ v ∈ S' \ S, a v := by
    rw [tprod_eq_prod (s := S' \ S)]
    · exact Finset.prod_congr rfl fun v hv => Set.mulIndicator_of_mem (Finset.mem_coe.mpr hv) a
    · intro v hv
      exact Set.mulIndicator_of_notMem (by rwa [Finset.mem_coe]) a
  rw [e1, e2, hsplit, Multipliable.tprod_mul (hmul _) (hmul _), hfin]

end GlobalTheory.CompanionTheory.SW.TailCut
