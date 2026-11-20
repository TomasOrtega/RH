import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibOfZero
open MeasureTheory Topology

namespace GlobalTheory.QuadFibre

/- English proof (translation)
Establish `hd : HasStrictDerivAt (fun x : K => x ^ 2) (2 : K) 1`. Simplify using `using hasStrictDerivAt_pow 2 (1 : K)`. Establish `hf` using `hd.hasStrictFDerivAt_equiv h2`. Set `e` to `hf.toOpenPartialHomeomorph _`. Establish `he : (e : K → K) = fun x => x ^ 2` using `hf.toOpenPartialHomeomorph_coe`.

Use `⟨e.target, e.symm, e.open_target, ?_, e.continuousOn_symm, fun u hu => ?_⟩` and prove the remaining obligations. Simplify using `using hf.image_mem_toOpenPartialHomeomorph_target`. Use `e.right_inv hu` as an intermediate fact. Rewrite `this` using `[he]`. Then use the resulting hypothesis.
-/
theorem exists_local_sqrt_near_one (K : Type) [NontriviallyNormedField K] [CompleteSpace K]
    (h2 : (2 : K) ≠ 0) : ∃ (N : Set K) (g : K → K), IsOpen N ∧ (1 : K) ∈ N ∧ ContinuousOn g N ∧
      ∀ u ∈ N, g u ^ 2 = u := by
  have hd : HasStrictDerivAt (fun x : K => x ^ 2) (2 : K) 1 := by
    simpa using hasStrictDerivAt_pow 2 (1 : K)
  have hf := hd.hasStrictFDerivAt_equiv h2
  let e := hf.toOpenPartialHomeomorph _
  have he : (e : K → K) = fun x => x ^ 2 := hf.toOpenPartialHomeomorph_coe
  refine ⟨e.target, e.symm, e.open_target, ?_, e.continuousOn_symm, fun u hu => ?_⟩
  · simpa using hf.image_mem_toOpenPartialHomeomorph_target
  · have := e.right_inv hu
    rwa [he] at this

/- English proof (translation)
Take `⟨N, g, hN, h1, hg, hsq⟩` from `exists_local_sqrt_near_one K h2`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 hN 1 h1`. Use `set r : ℝ := min (ε / 2) (1 / 2) with hr`. Establish `hr0 : 0 < r` using `lt_min (by linarith) (by norm_num)`. Establish `hrε : r < ε` using `lt_of_le_of_lt (min_le_left _ _) (by linarith)`.

Establish `hr1 : r < 1` using `lt_of_le_of_lt (min_le_right _ _) (by norm_num)`. Establish `hsub : Metric.closedBall (1 : K) r ⊆ N` using `(Metric.closedBall_subset_ball hrε).trans hball`. Establish `hopen : IsOpen (Metric.closedBall (1 : K) r)` using `IsUltrametricDist.isOpen_closedBall _ hr0.ne'`. Establish `hclopen : IsClopen (Metric.closedBall (1 : K) r)` using `⟨Metric.isClosed_closedBall, hopen⟩`. Establish `hnorm : ∀ a ∈ Metric.closedBall (1 : K) r, ‖a‖ = 1`.

Introduce `a ha`. Rewrite `ha` using `[mem_closedBall_iff_norm]`. Establish `hlt : ‖a - 1‖ < ‖(1 : K)‖` using `by rw [norm_one]; linarith`. Use `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, max_eq_right hlt.le, norm_one]`.

Conclude with `this`. Use `⟨Metric.closedBall 1 r, (Metric.closedBall (1 : K) r).piecewise g (fun _ => 1), hopen, isCompact_closedBall _ _, Metric.mem_closedBall_self hr0.le, ?_, ?_, hnorm, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha b hb`. Establish `hna` using `hnorm a ha`. Rewrite `ha`, `hb`, the goal using `[mem_closedBall_iff_norm]`.

Establish `: a * b - 1 = a * (b - 1) + (a - 1)` using `by ring`. Rewrite using `[this]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ha)` and prove the remaining obligations. Rewrite using `[norm_mul, hna, one_mul]` and apply the resulting hypothesis. Introduce `a ha`.

Establish `hna` using `hnorm a ha`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hna`. Rewrite `ha`, the goal using `[mem_closedBall_iff_norm]`.

Establish `: a⁻¹ - 1 = -(a⁻¹ * (a - 1))` using `by field_simp; ring`. Rewrite using `[this, norm_neg, norm_mul, norm_inv, hna, inv_one, one_mul]` and apply the resulting hypothesis. Use `continuous_piecewise ?_ ?_ continuousOn_const` and prove the remaining obligations. Simplify using `[hclopen.frontier_eq]`. Rewrite using `[Metric.isClosed_closedBall.closure_eq]`.

Conclude with `hg.mono hsub`. Introduce `a ha`. Rewrite using `[Set.piecewise_eq_of_mem _ _ _ ha]`. Conclude with `hsq a (hsub ha)`.
-/
theorem exists_isSqrtOn (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ProperSpace K] (h2 : (2 : K) ≠ 0) : ∃ (U : Set K) (s : K → K), IsSqrtOn U s := by
  classical
  obtain ⟨N, g, hN, h1, hg, hsq⟩ := exists_local_sqrt_near_one K h2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hN 1 h1
  set r : ℝ := min (ε / 2) (1 / 2) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr1 : r < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hsub : Metric.closedBall (1 : K) r ⊆ N :=
    (Metric.closedBall_subset_ball hrε).trans hball
  have hopen : IsOpen (Metric.closedBall (1 : K) r) :=
    IsUltrametricDist.isOpen_closedBall _ hr0.ne'
  have hclopen : IsClopen (Metric.closedBall (1 : K) r) := ⟨Metric.isClosed_closedBall, hopen⟩
  have hnorm : ∀ a ∈ Metric.closedBall (1 : K) r, ‖a‖ = 1 := by
    intro a ha
    rw [mem_closedBall_iff_norm] at ha
    have hlt : ‖a - 1‖ < ‖(1 : K)‖ := by rw [norm_one]; linarith
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
    rw [sub_add_cancel, max_eq_right hlt.le, norm_one] at this
    exact this
  refine ⟨Metric.closedBall 1 r, (Metric.closedBall (1 : K) r).piecewise g (fun _ => 1), hopen,
    isCompact_closedBall _ _, Metric.mem_closedBall_self hr0.le, ?_, ?_, hnorm, ?_, ?_⟩
  · intro a ha b hb
    have hna := hnorm a ha
    rw [mem_closedBall_iff_norm] at ha hb ⊢
    have : a * b - 1 = a * (b - 1) + (a - 1) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ha)
    rwa [norm_mul, hna, one_mul]
  · intro a ha
    have hna := hnorm a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hna
    rw [mem_closedBall_iff_norm] at ha ⊢
    have : a⁻¹ - 1 = -(a⁻¹ * (a - 1)) := by field_simp; ring
    rwa [this, norm_neg, norm_mul, norm_inv, hna, inv_one, one_mul]
  · refine continuous_piecewise ?_ ?_ continuousOn_const
    · simp [hclopen.frontier_eq]
    · rw [Metric.isClosed_closedBall.closure_eq]
      exact hg.mono hsub
  · intro a ha
    rw [Set.piecewise_eq_of_mem _ _ _ ha]
    exact hsq a (hsub ha)

end GlobalTheory.QuadFibre
