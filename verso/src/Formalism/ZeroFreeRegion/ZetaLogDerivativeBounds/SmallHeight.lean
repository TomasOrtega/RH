import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

open Complex Set Filter Topology

noncomputable section

namespace Formalism.ZF

/- English proof (translation)
Unfold `SmallHeight`. Introduce `T`. Establish `hopen : IsOpen {s : ℂ | s ≠ 1 → riemannZeta s ≠ 0}`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `z hz`.

Distinguish the cases in `hz1 : z = 1`. Substitute `hz1` using the available equality. Establish `h` using `riemannZeta_residue_one.eventually_ne one_ne_zero`. Rewrite `h` using `[eventually_nhdsWithin_iff]`. Use `filter_upwards [h] with x hx hx1`.

Conclude with `right_ne_zero_of_mul (hx hx1)`. Establish `hc : ContinuousAt riemannZeta z` using `(differentiableAt_riemannZeta hz1).continuousAt filter_upwards [hc.eventually_ne (hz hz1)] with x hx _`. Conclude with `hx`. Use `set K : Set ℂ := (fun y : ℝ => (1 : ℂ) + (y : ℂ) * I) '' Icc (-T) T`. Establish `hKc : IsCompact K` using `isCompact_Icc.image (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))`.

Establish `hKsub : K ⊆ {s : ℂ | s ≠ 1 → riemannZeta s ≠ 0}`. Introduce and unpack `_ ⟨y, -, rfl⟩ _`. Apply `riemannZeta_ne_zero_of_one_le_re` to reduce the goal to its premises. Simplify using the standard rewrite rules. Take `⟨δ, hδ, hsub⟩` from `hKc.exists_cthickening_subset_open hopen hKsub`.

Use `⟨δ, hδ, fun s hs hre hs1 => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hle : 1 ≤ s.re`. Conclude with `riemannZeta_ne_zero_of_one_le_re hle`. Use `push_neg at hle`. Establish `hp : (1 : ℂ) + (s.im : ℂ) * I ∈ K` using `⟨s.im, abs_le.mp hs, rfl⟩`.

Establish `hre1 : ((1 : ℂ) + (s.im : ℂ) * I).re = 1` using `by simp`. Establish `him1 : s.im = ((1 : ℂ) + (s.im : ℂ) * I).im` using `by simp`. Establish `hd : dist s ((1 : ℂ) + (s.im : ℂ) * I) ≤ δ`. Rewrite using `[Complex.dist_of_im_eq him1, Real.dist_eq, hre1, abs_le]`. Apply the tactic sequence `constructor <;> linarith`.

Conclude with `hsub (Metric.mem_cthickening_of_dist_le _ _ _ _ hp hd) hs1`.
-/
theorem zeroFreeBoundedHeight : SmallHeight := by
  unfold SmallHeight
  intro T
  have hopen : IsOpen {s : ℂ | s ≠ 1 → riemannZeta s ≠ 0} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    by_cases hz1 : z = 1
    · subst hz1
      have h := riemannZeta_residue_one.eventually_ne one_ne_zero
      rw [eventually_nhdsWithin_iff] at h
      filter_upwards [h] with x hx hx1
      exact right_ne_zero_of_mul (hx hx1)
    · have hc : ContinuousAt riemannZeta z := (differentiableAt_riemannZeta hz1).continuousAt
      filter_upwards [hc.eventually_ne (hz hz1)] with x hx _
      exact hx
  set K : Set ℂ := (fun y : ℝ => (1 : ℂ) + (y : ℂ) * I) '' Icc (-T) T
  have hKc : IsCompact K :=
    isCompact_Icc.image (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have hKsub : K ⊆ {s : ℂ | s ≠ 1 → riemannZeta s ≠ 0} := by
    rintro _ ⟨y, -, rfl⟩ _
    apply riemannZeta_ne_zero_of_one_le_re
    simp
  obtain ⟨δ, hδ, hsub⟩ := hKc.exists_cthickening_subset_open hopen hKsub
  refine ⟨δ, hδ, fun s hs hre hs1 => ?_⟩
  by_cases hle : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hle
  · push_neg at hle
    have hp : (1 : ℂ) + (s.im : ℂ) * I ∈ K := ⟨s.im, abs_le.mp hs, rfl⟩
    have hre1 : ((1 : ℂ) + (s.im : ℂ) * I).re = 1 := by simp
    have him1 : s.im = ((1 : ℂ) + (s.im : ℂ) * I).im := by simp
    have hd : dist s ((1 : ℂ) + (s.im : ℂ) * I) ≤ δ := by
      rw [Complex.dist_of_im_eq him1, Real.dist_eq, hre1, abs_le]
      constructor <;> linarith
    exact hsub (Metric.mem_cthickening_of_dist_le _ _ _ _ hp hd) hs1

end Formalism.ZF
