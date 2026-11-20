import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut

noncomputable section

open Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open GlobalTheory.Cont

/- English proof (translation)
Introduce `U _ hU`. Take `⟨⟨σ, hσ⟩, hR⟩` from `hU`. Use `isPreconnected_of_forall (((σ + 1 : ℝ)) : ℂ) fun y hy => ?_` and prove the remaining obligations. Establish `hx : (((σ + 1 : ℝ)) : ℂ) ∈ rightOf σ` using `by show σ < (((σ + 1 : ℝ)) : ℂ).re`. Simplify using the standard rewrite rules.

Use `set T : ℝ := |y.re| + |σ| + 1 with hTdef`. Establish `hT : (y + (T : ℂ)) ∈ rightOf σ` using `by show σ < (y + (T : ℂ)).re`. Simplify using `only [Complex.add_re, Complex.ofReal_re, hTdef]`. Combine the linear relations using `[neg_abs_le y.re, le_abs_self σ]`. Establish `hconv : Convex ℝ (rightOf σ)` using `convex_halfSpace_re_gt σ`.

Use `⟨segment ℝ y (y + (T : ℂ)) ∪ segment ℝ (y + (T : ℂ)) (((σ + 1 : ℝ)) : ℂ), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `Set.union_subset ?_ ((hconv.segment_subset hT hx).trans hσ)` and prove the remaining obligations. Introduce and unpack `z ⟨a, b, ha, hb, hab, rfl⟩`. Establish `hab' : (a : ℂ) + (b : ℂ) = 1` using `by exact_mod_cast hab`. Establish `heq : a • y + b • (y + (T : ℂ)) = y + ((b * T : ℝ) : ℂ)`.

Simplify using `only [Complex.real_smul]`. Use `push_cast`. Take the linear combination `y * hab'`. Rewrite using `[heq]`. Conclude with `hR y hy _ (mul_nonneg hb (by positivity))`.

Conclude with `Or.inr (right_mem_segment _ _ _)`. Conclude with `Or.inl (left_mem_segment _ _ _)`. Conclude with `IsPreconnected.union (y + (T : ℂ)) (right_mem_segment _ _ _) (left_mem_segment _ _ _) (convex_segment _ _).isPreconnected (convex_segment _ _).isPreconnected`.
-/
theorem rightConn : RightConn := by
  intro U _ hU
  obtain ⟨⟨σ, hσ⟩, hR⟩ := hU
  refine isPreconnected_of_forall (((σ + 1 : ℝ)) : ℂ) fun y hy => ?_
  have hx : (((σ + 1 : ℝ)) : ℂ) ∈ rightOf σ := by
    show σ < (((σ + 1 : ℝ)) : ℂ).re
    simp
  set T : ℝ := |y.re| + |σ| + 1 with hTdef
  have hT : (y + (T : ℂ)) ∈ rightOf σ := by
    show σ < (y + (T : ℂ)).re
    simp only [Complex.add_re, Complex.ofReal_re, hTdef]
    linarith [neg_abs_le y.re, le_abs_self σ]
  have hconv : Convex ℝ (rightOf σ) := convex_halfSpace_re_gt σ
  refine ⟨segment ℝ y (y + (T : ℂ)) ∪ segment ℝ (y + (T : ℂ)) (((σ + 1 : ℝ)) : ℂ), ?_, ?_, ?_, ?_⟩
  · refine Set.union_subset ?_ ((hconv.segment_subset hT hx).trans hσ)
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    have heq : a • y + b • (y + (T : ℂ)) = y + ((b * T : ℝ) : ℂ) := by
      simp only [Complex.real_smul]
      push_cast
      linear_combination y * hab'
    rw [heq]
    exact hR y hy _ (mul_nonneg hb (by positivity))
  · exact Or.inr (right_mem_segment _ _ _)
  · exact Or.inl (left_mem_segment _ _ _)
  · exact IsPreconnected.union (y + (T : ℂ)) (right_mem_segment _ _ _) (left_mem_segment _ _ _)
      (convex_segment _ _).isPreconnected (convex_segment _ _).isPreconnected

/- English proof (translation)
Introduce `U f h σ s₀ hUo hU hs₀ hfm hfa hσU hhd hfh`. Take `⟨H, hH⟩ : ∃ H : ℂ → ℂ, ∀ w, H w = if σ + 1 < w.re then h w else f w` from `⟨_, fun _ => rfl⟩`. Establish `hHf : ∀ z, H =ᶠ[𝓝[≠] z] f`. Introduce `z`. Distinguish the cases in `hz : σ < z.re`.

Use `filter_upwards [hfh z hz] with w hw`. Rewrite using `[hH]`. Use `split_ifs`. Conclude with `hw.symm`. Both sides reduce to the same expression.

Establish `hlt : z.re < σ + 1` using `by linarith [not_lt.1 hz]`. Establish `hn : {w : ℂ | w.re < σ + 1} ∈ 𝓝 z` using `Complex.continuous_re.continuousAt.preimage_mem_nhds (Iio_mem_nhds hlt)`. Use `filter_upwards [nhdsWithin_le_nhds hn] with w hw`. Rewrite using `[hH, if_neg (not_lt.2 (le_of_lt hw))]`. Establish `hmer : IsMerExt h U H`.

Use `⟨hU, fun z hz => (hfm z hz).congr (hHf z).symm, σ + 1, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[hH, if_pos (show σ + 1 < z.re from hz)]`. Establish `hext : IsExtAt h s₀ (Function.update H s₀ (f s₀))` using `(hmer.isExtAt hs₀).update _`. Use `⟨_, hext, ?_, by simp⟩` and prove the remaining obligations. Apply `hfa.congr` to reduce the goal to its premises.

Establish `h2` using `eventually_nhdsWithin_iff.1 (hHf s₀)`. Use `filter_upwards [h2] with w hw`. Distinguish the cases in `hw0 : w = s₀`. Substitute `hw0` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Function.update_of_ne hw0]`. Conclude with `(hw hw0).symm`.
-/
theorem glue : Glue := by
  intro U f h σ s₀ hUo hU hs₀ hfm hfa hσU hhd hfh
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℂ, ∀ w, H w = if σ + 1 < w.re then h w else f w := ⟨_, fun _ => rfl⟩
  have hHf : ∀ z, H =ᶠ[𝓝[≠] z] f := by
    intro z
    by_cases hz : σ < z.re
    · filter_upwards [hfh z hz] with w hw
      rw [hH]
      split_ifs
      · exact hw.symm
      · rfl
    · have hlt : z.re < σ + 1 := by linarith [not_lt.1 hz]
      have hn : {w : ℂ | w.re < σ + 1} ∈ 𝓝 z :=
        Complex.continuous_re.continuousAt.preimage_mem_nhds (Iio_mem_nhds hlt)
      filter_upwards [nhdsWithin_le_nhds hn] with w hw
      rw [hH, if_neg (not_lt.2 (le_of_lt hw))]
  have hmer : IsMerExt h U H := by
    refine ⟨hU, fun z hz => (hfm z hz).congr (hHf z).symm, σ + 1, fun z hz => ?_⟩
    rw [hH, if_pos (show σ + 1 < z.re from hz)]
  have hext : IsExtAt h s₀ (Function.update H s₀ (f s₀)) := (hmer.isExtAt hs₀).update _
  refine ⟨_, hext, ?_, by simp⟩
  apply hfa.congr
  have h2 := eventually_nhdsWithin_iff.1 (hHf s₀)
  filter_upwards [h2] with w hw
  by_cases hw0 : w = s₀
  · subst hw0
    simp
  · rw [Function.update_of_ne hw0]
    exact (hw hw0).symm

end PositivityTheory.Rg.Sw.AbsSt
