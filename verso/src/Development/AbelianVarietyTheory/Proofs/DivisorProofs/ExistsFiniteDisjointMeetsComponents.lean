import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

/- English proof (translation)
Use `haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩`. Take `⟨r, hr, hsub⟩` from `Metric.isOpen_iff.1 e.open_target (e x) (e.map_source hx)`. Use `⟨e.symm '' ball (e x) r, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `e.symm.image_mem_nhds (x := e x) (e.map_source hx) (ball_mem_nhds (e x) hr)`. Rewrite `h` using `[e.left_inv hx]`. Then use the resulting hypothesis.

Conclude with `(convex_ball (e x) r).isPreconnected.image _ (e.continuousOn_symm.mono hsub)`. Use `Set.Infinite.image (e.symm.injOn.mono hsub) ?_ haveI : NeBot (𝓝[≠] (e x)) := Module.punctured_nhds_neBot ℂ (V n) (e x)` and prove the remaining obligations. Conclude with `infinite_of_mem_nhds (e x) (ball_mem_nhds (e x) hr)`.
-/
theorem exists_preconnected_infinite_nhds {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (hn : 1 ≤ n) (e : OpenPartialHomeomorph Y (V n)) (x : Y) (hx : x ∈ e.source) :
    ∃ B : Set Y, B ∈ 𝓝 x ∧ IsPreconnected B ∧ B.Infinite := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 e.open_target (e x) (e.map_source hx)
  refine ⟨e.symm '' ball (e x) r, ?_, ?_, ?_⟩
  · have h := e.symm.image_mem_nhds (x := e x) (e.map_source hx) (ball_mem_nhds (e x) hr)
    rwa [e.left_inv hx] at h
  · exact (convex_ball (e x) r).isPreconnected.image _ (e.continuousOn_symm.mono hsub)
  · refine Set.Infinite.image (e.symm.injOn.mono hsub) ?_
    haveI : NeBot (𝓝[≠] (e x)) := Module.punctured_nhds_neBot ℂ (V n) (e x)
    exact infinite_of_mem_nhds (e x) (ball_mem_nhds (e x) hr)

/- English proof (translation)
Introduce `n Y _ _ _ _ _ _ ι La _ A hn S hS`. Establish `h1 : ∀ x : Y, ∃ B : Set Y, B ∈ 𝓝 x ∧ IsPreconnected B ∧ ∃ P ∈ B, P ∉ S`. Introduce `x`. Take `⟨B, hB, hc, hi⟩` from `exists_preconnected_infinite_nhds hn (A.chart (A.pick x)) x (A.mem_pick x)`. Take `⟨P, hP, hPS⟩` from `(hi.diff hS).nonempty`.

Conclude with `⟨B, hB, hc, P, hP, hPS⟩`. Use `choose B hB hc P hP hPS using h1`. Take `⟨t, -, ht⟩` from `isCompact_univ.elim_nhds_subcover B (fun x _ => hB x)`. Use `⟨P '' (t : Set Y), t.finite_toSet.image P, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.disjoint_left]`.

Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `hPS x`. Introduce `y`. Take `⟨x, hx, hy⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ y))`. Conclude with `⟨P x, ⟨x, hx, rfl⟩, (hc x).subset_connectedComponent hy (hP x)⟩`.
-/
theorem exists_finite_disjoint_meets_components :
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → ∀ S : Set Y, S.Finite → ∃ T : Set Y, T.Finite ∧ Disjoint T S ∧ ∀ y, ∃ P ∈ T, P ∈ connectedComponent y := by
  intro n Y _ _ _ _ _ _ ι La _ A hn S hS
  have h1 : ∀ x : Y, ∃ B : Set Y, B ∈ 𝓝 x ∧ IsPreconnected B ∧ ∃ P ∈ B, P ∉ S := by
    intro x
    obtain ⟨B, hB, hc, hi⟩ :=
      exists_preconnected_infinite_nhds hn (A.chart (A.pick x)) x (A.mem_pick x)
    obtain ⟨P, hP, hPS⟩ := (hi.diff hS).nonempty
    exact ⟨B, hB, hc, P, hP, hPS⟩
  choose B hB hc P hP hPS using h1
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover B (fun x _ => hB x)
  refine ⟨P '' (t : Set Y), t.finite_toSet.image P, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨x, -, rfl⟩
    exact hPS x
  · intro y
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨P x, ⟨x, hx, rfl⟩, (hc x).subset_connectedComponent hy (hP x)⟩

end GlobalTheory.OTY
