import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

/- English proof (translation)
Establish `hK : IsCompact (Metric.closedBall z r)` using `isCompact_closedBall z r`. Establish `hpos : ∀ w ∈ Metric.closedBall z r, 0 < w.re`. Introduce `w hw`. Establish `h1 : ‖w - z‖ ≤ r` using `by simpa [dist_eq_norm] using hw`. Establish `h2 : |(w - z).re| ≤ ‖w - z‖` using `Complex.abs_re_le_norm _`.

Establish `h3` using `(abs_le.mp (h2.trans h1)).1`. Simplify using `only [Complex.sub_re] at h3`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨t, -, ht⟩` from `hK.elim_nhds_subcover (fun w => {v | v ∈ ({w}ᶜ : Set ℂ) → v ∉ Z}) (fun w hw => eventually_nhdsWithin_iff.mp (hiso w (hpos w hw)))`. Use `t.finite_toSet.subset ?_` and prove the remaining obligations.

Introduce and unpack `v ⟨hvZ, hvK⟩`. Take `⟨w, hw, hvw⟩` from `Set.mem_iUnion₂.mp (ht hvK)`. Distinguish the cases in `h : v = w`. Rewrite using `[h]`. Conclude with `hw`.

Conclude with `absurd hvZ (hvw h)`.
-/
theorem landau_finite {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {z : ℂ} {r : ℝ}
    (hr : r < z.re) : (Z ∩ Metric.closedBall z r).Finite := by
  have hK : IsCompact (Metric.closedBall z r) := isCompact_closedBall z r
  have hpos : ∀ w ∈ Metric.closedBall z r, 0 < w.re := by
    intro w hw
    have h1 : ‖w - z‖ ≤ r := by simpa [dist_eq_norm] using hw
    have h2 : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm _
    have h3 := (abs_le.mp (h2.trans h1)).1
    simp only [Complex.sub_re] at h3
    linarith
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun w => {v | v ∈ ({w}ᶜ : Set ℂ) → v ∉ Z})
    (fun w hw => eventually_nhdsWithin_iff.mp (hiso w (hpos w hw)))
  refine t.finite_toSet.subset ?_
  rintro v ⟨hvZ, hvK⟩
  obtain ⟨w, hw, hvw⟩ := Set.mem_iUnion₂.mp (ht hvK)
  by_cases h : v = w
  · rw [h]; exact hw
  · exact absurd hvZ (hvw h)

end Deduction

end
