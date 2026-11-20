import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F}

/- English proof (translation)
Take `⟨W, ι, _, g, G, O, h₁, h₂, h₃, h₄, h₅⟩` from `h`. Use `⟨W, ι, inferInstance, g, fun v => (G v)⁻¹, O ∩ G ⁻¹' {0}ᶜ, h₁, h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_compl_singleton, ⟨h₃, ?_⟩, (h₄.mono Set.inter_subset_left).inv fun _ hv => hv.2, ?_⟩` and prove the remaining obligations. Conclude with `fun e => h0 (h₅.eq_of_nhds.trans e)`. Use `filter_upwards [h₅] with z e`. Rewrite using `[e]`.
-/
theorem cInfAt_inv_of_ne_zero {f : CxPts X.str σ → ℝ} {y : CxPts X.str σ} (h : CInfAt f y)
    (h0 : f y ≠ 0) : CInfAt (fun z => (f z)⁻¹) y := by
  obtain ⟨W, ι, _, g, G, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨W, ι, inferInstance, g, fun v => (G v)⁻¹, O ∩ G ⁻¹' {0}ᶜ, h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_compl_singleton, ⟨h₃, ?_⟩,
    (h₄.mono Set.inter_subset_left).inv fun _ hv => hv.2, ?_⟩
  · exact fun e => h0 (h₅.eq_of_nhds.trans e)
  · filter_upwards [h₅] with z e
    rw [e]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using cInfAt_const 0 y`. Consider the case `insert a s ha ih => simpa only [Finset.sum_insert ha] using (h a).add ih`.
-/
theorem cInfAt_finset_sum {ι : Type} (s : Finset ι) {f : ι → CxPts X.str σ → ℝ}
    {y : CxPts X.str σ} (h : ∀ i, CInfAt (f i) y) : CInfAt (fun z => ∑ i ∈ s, f i z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const 0 y
  | insert a s ha ih => simpa only [Finset.sum_insert ha] using (h a).add ih

/- English proof (translation)
Use `haveI := CxPts.compactSpace σ X.isProjOver`. Use `haveI := CxPts.t2Space_cxPts_of_isProjOver σ X.isProjOver`. Take `⟨c, hc⟩` from `AlgChart.exists_mem_source (D := X.dim) y`. Take `⟨K, hKy, hKc, hKV⟩` from `exists_mem_nhds_isClosed_subset (inter_mem hU (c.e.open_source.mem_nhds hc))`. Establish `hn : c.e.symm ⁻¹' K ∈ 𝓝 (c.e y)` using `c.e.continuousAt_symm (c.e.map_source hc) (by rwa [c.e.left_inv hc])`.

Take `⟨r, hr, hrO⟩` from `Metric.mem_nhds_iff.1 hn`. Set `b : ContDiffBump (c.e y)` to `⟨r / 2, r, half_pos hr, half_lt_self hr⟩`. Establish `hsupp : ∀ z ∈ c.e.source, b (c.e z) ≠ 0 → z ∈ K`. Introduce `z hz h`. Establish `h₁ : c.e z ∈ Metric.ball (c.e y) r`.

Establish `: c.e z ∈ Function.support b` using `h`. Rewrite `this` using `[b.support_eq]`. Then use the resulting hypothesis. Establish `h₂ : c.e.symm (c.e z) ∈ K` using `hrO h₁`. Rewrite `h₂` using `[c.e.left_inv hz]`. Then use the resulting hypothesis. Use `⟨fun z => if z ∈ c.e.source then b (c.e z) else 0, fun z => ?_, fun z => ?_, ?_, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hz : z ∈ c.e.source`. Use `cInfAt_of_chart isOpen_univ c ?_ hz trivial` and prove the remaining obligations. Use `(b.contDiff (n := ⊤)).contDiffOn.congr fun v hv => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, if_pos (c.e.map_target hv.1), c.e.right_inv hv.1]`. Establish `hzK : z ∉ K` using `fun h => hz (hKV h).2`.

Use `(cInfAt_const 0 z).congr ?_` and prove the remaining obligations. Use `filter_upwards [hKc.isOpen_compl.mem_nhds hzK] with w hw`. Distinguish the cases in `hwS : w ∈ c.e.source`. Simplify using `only [if_pos hwS]`. Assume the negation of the conclusion as `h`.

Conclude with `hw (hsupp w hwS h)`. Simplify using `only [if_neg hwS]`. Simplify using `only split_ifs`. Conclude with `b.nonneg`. Conclude with `le_rfl`.

Simplify using `only [if_pos hc]`. Rewrite using `[b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]`. Conclude with `one_pos`. Use `(closure_minimal (fun z hz => ?_) hKc).trans fun z hz => (hKV hz).1` and prove the remaining obligations. Distinguish the cases in `hzS : z ∈ c.e.source`.

Conclude with `hsupp z hzS (by simpa only [Function.mem_support, if_pos hzS] using hz)`. Simplify using `only [Function.mem_support, if_neg hzS, ne_eq, not_true_eq_false] at hz`.
-/
theorem exists_cInf_bump (y : CxPts X.str σ) {U : Set (CxPts X.str σ)} (hU : U ∈ 𝓝 y) :
    ∃ χ : CxPts X.str σ → ℝ, (∀ z, CInfAt χ z) ∧ (∀ z, 0 ≤ χ z) ∧ 0 < χ y ∧ tsupport χ ⊆ U := by
  classical
  haveI := CxPts.compactSpace σ X.isProjOver
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ X.isProjOver
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := X.dim) y
  obtain ⟨K, hKy, hKc, hKV⟩ :=
    exists_mem_nhds_isClosed_subset (inter_mem hU (c.e.open_source.mem_nhds hc))
  have hn : c.e.symm ⁻¹' K ∈ 𝓝 (c.e y) :=
    c.e.continuousAt_symm (c.e.map_source hc) (by rwa [c.e.left_inv hc])
  obtain ⟨r, hr, hrO⟩ := Metric.mem_nhds_iff.1 hn
  let b : ContDiffBump (c.e y) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hsupp : ∀ z ∈ c.e.source, b (c.e z) ≠ 0 → z ∈ K := by
    intro z hz h
    have h₁ : c.e z ∈ Metric.ball (c.e y) r := by
      have : c.e z ∈ Function.support b := h
      rwa [b.support_eq] at this
    have h₂ : c.e.symm (c.e z) ∈ K := hrO h₁
    rwa [c.e.left_inv hz] at h₂
  refine ⟨fun z => if z ∈ c.e.source then b (c.e z) else 0, fun z => ?_, fun z => ?_, ?_, ?_⟩
  · by_cases hz : z ∈ c.e.source
    · refine cInfAt_of_chart isOpen_univ c ?_ hz trivial
      refine (b.contDiff (n := ⊤)).contDiffOn.congr fun v hv => ?_
      simp only [Function.comp_apply, if_pos (c.e.map_target hv.1), c.e.right_inv hv.1]
    · have hzK : z ∉ K := fun h => hz (hKV h).2
      refine (cInfAt_const 0 z).congr ?_
      filter_upwards [hKc.isOpen_compl.mem_nhds hzK] with w hw
      by_cases hwS : w ∈ c.e.source
      · simp only [if_pos hwS]
        by_contra h
        exact hw (hsupp w hwS h)
      · simp only [if_neg hwS]
  · dsimp only
    split_ifs
    · exact b.nonneg
    · exact le_rfl
  · simp only [if_pos hc]
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    exact one_pos
  · refine (closure_minimal (fun z hz => ?_) hKc).trans fun z hz => (hKV hz).1
    by_cases hzS : z ∈ c.e.source
    · exact hsupp z hzS (by simpa only [Function.mem_support, if_pos hzS] using hz)
    · simp only [Function.mem_support, if_neg hzS, ne_eq, not_true_eq_false] at hz

/- English proof (translation)
Introduce `F _ σ X W hW`. Use `haveI := CxPts.compactSpace σ X.isProjOver`. Use `choose χ hχ h0 hpos hs using fun y => exists_cInf_bump y (hW y)`. Take `⟨s, hcov⟩` from `CompactSpace.elim_nhds_subcover (fun y => {z | 0 < χ y z}) fun y => (hχ y y).continuousAt.eventually (lt_mem_nhds (hpos y))`. Establish `hT (z) : ∑ i : s, χ i z ≠ 0`.

Establish `hz : z ∈ ⋃ y ∈ s, {z | 0 < χ y z}` using `hcov ▸ Set.mem_univ z`. Take `⟨y, hy, hz⟩` from `Set.mem_iUnion₂.1 hz`. Conclude with `(Finset.sum_pos' (f := fun i : s => χ i z) (fun i _ => h0 i z) ⟨⟨y, hy⟩, Finset.mem_univ _, hz⟩).ne'`. Use `⟨s, fun i z => χ i z * (∑ j : s, χ j z)⁻¹, fun i y => ?_, fun i => (tsupport_mul_subset_left).trans (hs i), fun y => ?_⟩` and prove the remaining obligations. Conclude with `(hχ i y).comp₂ (cInfAt_inv_of_ne_zero (cInfAt_finset_sum Finset.univ fun j : s => hχ j y) (hT y)) (G := fun x => x.1 * x.2) (contDiff_fst.mul contDiff_snd)`.

Rewrite using `[← Finset.sum_mul, mul_inv_cancel₀ (hT y)]`.
-/
theorem exists_cInf_partition : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} (W : CxPts X.str σ → Set (CxPts X.str σ)), (∀ y, W y ∈ 𝓝 y) → ∃ (s : Finset (CxPts X.str σ)) (ρ : s → CxPts X.str σ → ℝ), (∀ i y, CInfAt (ρ i) y) ∧ (∀ i, tsupport (ρ i) ⊆ W i) ∧ ∀ y, ∑ i, ρ i y = 1 := by
  intro F _ σ X W hW
  haveI := CxPts.compactSpace σ X.isProjOver
  choose χ hχ h0 hpos hs using fun y => exists_cInf_bump y (hW y)
  obtain ⟨s, hcov⟩ := CompactSpace.elim_nhds_subcover (fun y => {z | 0 < χ y z})
    fun y => (hχ y y).continuousAt.eventually (lt_mem_nhds (hpos y))
  have hT (z) : ∑ i : s, χ i z ≠ 0 := by
    have hz : z ∈ ⋃ y ∈ s, {z | 0 < χ y z} := hcov ▸ Set.mem_univ z
    obtain ⟨y, hy, hz⟩ := Set.mem_iUnion₂.1 hz
    exact (Finset.sum_pos' (f := fun i : s => χ i z) (fun i _ => h0 i z)
      ⟨⟨y, hy⟩, Finset.mem_univ _, hz⟩).ne'
  refine ⟨s, fun i z => χ i z * (∑ j : s, χ j z)⁻¹, fun i y => ?_,
    fun i => (tsupport_mul_subset_left).trans (hs i), fun y => ?_⟩
  · exact (hχ i y).comp₂ (cInfAt_inv_of_ne_zero
      (cInfAt_finset_sum Finset.univ fun j : s => hχ j y) (hT y))
      (G := fun x => x.1 * x.2) (contDiff_fst.mul contDiff_snd)
  · rw [← Finset.sum_mul, mul_inv_cancel₀ (hT y)]

end GlobalTheory.GoodTop
