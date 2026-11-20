import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDensityExists
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

/- English proof (translation)
Introduce `k _ X _ p D hX hS σ`. Use `haveI := hX.compactSpace σ`. Use `haveI := CxPts.t2Space_cxPts_of_isProjOver σ hX.isProjOver`. Take `⟨R⟩` from `hS σ`. Take `⟨s, hs⟩` from `R.exists_finite`.

Take `⟨f, hf⟩` from `PartitionOfUnity.exists_isSubordinate (X := CxPts p σ) (ι := s) isClosed_univ (fun i => (R.chart i.1).e.source) (fun i => (R.chart i.1).e.open_source) (fun y _ => by`. Take `⟨i, hi, hy⟩` from `hs y`. Conclude with `Set.mem_iUnion.2 ⟨⟨i, hi⟩, hy⟩)`. Establish `hsrc : ∀ (i : s) (y : CxPts p σ), f i y ≠ 0 → y ∈ (R.chart i.1).e.source` using `fun i y h => hf i (subset_tsupport _ h)`. Use `⟨{ dens := fun c y => ∑ i : s, f i y * ‖ChartGlue.transDet c.e (R.chart i.1).e y‖ ^ 2 cont := fun c => ?_ pos := fun c y hy => ?_ trans := fun c c' y hy hy' => ?_ }⟩` and prove the remaining obligations.

Use `continuousOn_finset_sum _ fun i _ => fun y hy => ContinuousAt.continuousWithinAt ?_` and prove the remaining obligations. Distinguish the cases in `h : y ∈ tsupport (f i)`. Conclude with `(f i).continuous.continuousAt.mul ((CurveDens.continuousAt_transDet_chart c _ hy (hf i h)).norm.pow 2)`. Use `(continuousAt_const (y := (0 : ℝ))).congr ?_ filter_upwards [notMem_tsupport_iff_eventuallyEq.1 h] with z hz` and prove the remaining obligations. Rewrite using `[hz, Pi.zero_apply, zero_mul]`.

Take `⟨i, hi⟩` from `f.exists_pos (Set.mem_univ y)`. Use `Finset.sum_pos' (fun j _ => mul_nonneg (f.nonneg j y) (sq_nonneg _)) ⟨i, Finset.mem_univ _, mul_pos hi (pow_pos (norm_pos_iff.2 ?_) 2)⟩` and prove the remaining obligations. Conclude with `CurveDens.transDet_chart_ne_zero c _ hy (hsrc i y hi.ne')`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Distinguish the cases in `h : f i y = 0`. Simplify using `[h]`. Rewrite using `[CurveDens.transDet_trans_chart c c' _ hy hy' (hsrc i y h), norm_mul, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_volDens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → GenSmooth p D → ∀ σ : k →+* ℂ, Nonempty (VolDens p σ D) := by
  intro k _ X _ p D hX hS σ
  haveI := hX.compactSpace σ
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hX.isProjOver
  obtain ⟨R⟩ := hS σ
  obtain ⟨s, hs⟩ := R.exists_finite
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate (X := CxPts p σ) (ι := s) isClosed_univ
    (fun i => (R.chart i.1).e.source) (fun i => (R.chart i.1).e.open_source)
    (fun y _ => by
      obtain ⟨i, hi, hy⟩ := hs y
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hy⟩)
  have hsrc : ∀ (i : s) (y : CxPts p σ), f i y ≠ 0 → y ∈ (R.chart i.1).e.source := fun i y h =>
    hf i (subset_tsupport _ h)
  refine ⟨{ dens := fun c y => ∑ i : s, f i y * ‖ChartGlue.transDet c.e (R.chart i.1).e y‖ ^ 2
            cont := fun c => ?_
            pos := fun c y hy => ?_
            trans := fun c c' y hy hy' => ?_ }⟩
  · refine continuousOn_finset_sum _ fun i _ => fun y hy => ContinuousAt.continuousWithinAt ?_
    by_cases h : y ∈ tsupport (f i)
    · exact (f i).continuous.continuousAt.mul
        ((CurveDens.continuousAt_transDet_chart c _ hy (hf i h)).norm.pow 2)
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 h] with z hz
      rw [hz, Pi.zero_apply, zero_mul]
  · obtain ⟨i, hi⟩ := f.exists_pos (Set.mem_univ y)
    refine Finset.sum_pos' (fun j _ => mul_nonneg (f.nonneg j y) (sq_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos hi (pow_pos (norm_pos_iff.2 ?_) 2)⟩
    exact CurveDens.transDet_chart_ne_zero c _ hy (hsrc i y hi.ne')
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : f i y = 0
    · simp [h]
    · rw [CurveDens.transDet_trans_chart c c' _ hy hy' (hsrc i y h), norm_mul, mul_pow]
      ring

end GlobalTheory.HSAmp
