import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent

noncomputable section

open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

/- English proof (translation)
Introduce `H _ _ _ a ha`. Use `⟨cfc (fun x : ℝ => max x 0) a, cfc (fun x : ℝ => max (-x) 0) a, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← cfc_sub (fun x : ℝ => max x 0) (fun x : ℝ => max (-x) 0) a] conv_lhs => rw [← cfc_id' ℝ a]`. Use `cfc_congr fun x _ => ?_` and prove the remaining obligations. Conclude with `(max_zero_sub_eq_self x).symm`.

Rewrite using `[← cfc_mul (fun x : ℝ => max (-x) 0) (fun x : ℝ => max x 0) a]`. Rewrite using `[← cfc_zero ℝ a]`. Use `cfc_congr fun x _ => ?_` and prove the remaining obligations. Break down `le_total x 0 with h | h` into its components or cases. Simplify using `[max_eq_right h]`.

Simplify using `[max_eq_right (neg_nonpos.mpr h)]`. Introduce `x`. Establish `hp : 0 ≤ cfc (fun x : ℝ => max x 0) a` using `cfc_nonneg fun y _ => le_max_right _ _`. Conclude with `((ContinuousLinearMap.nonneg_iff_isPositive _).mp hp).re_inner_nonneg_left x`. Introduce `x`.

Establish `hm : 0 ≤ cfc (fun x : ℝ => max (-x) 0) a` using `cfc_nonneg fun y _ => le_max_right _ _`. Conclude with `((ContinuousLinearMap.nonneg_iff_isPositive _).mp hm).re_inner_nonneg_left x`. Introduce `S hS`. Conclude with `⟨hS.cfc_real _, hS.cfc_real _⟩`.
-/
theorem positive_negative_holds : PosNeg := by
  intro H _ _ _ a ha
  refine ⟨cfc (fun x : ℝ => max x 0) a, cfc (fun x : ℝ => max (-x) 0) a, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← cfc_sub (fun x : ℝ => max x 0) (fun x : ℝ => max (-x) 0) a]
    conv_lhs => rw [← cfc_id' ℝ a]
    refine cfc_congr fun x _ => ?_
    exact (max_zero_sub_eq_self x).symm
  · rw [← cfc_mul (fun x : ℝ => max (-x) 0) (fun x : ℝ => max x 0) a]
    rw [← cfc_zero ℝ a]
    refine cfc_congr fun x _ => ?_
    rcases le_total x 0 with h | h
    · simp [max_eq_right h]
    · simp [max_eq_right (neg_nonpos.mpr h)]
  · intro x
    have hp : 0 ≤ cfc (fun x : ℝ => max x 0) a := cfc_nonneg fun y _ => le_max_right _ _
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hp).re_inner_nonneg_left x
  · intro x
    have hm : 0 ≤ cfc (fun x : ℝ => max (-x) 0) a := cfc_nonneg fun y _ => le_max_right _ _
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hm).re_inner_nonneg_left x
  · intro S hS
    exact ⟨hS.cfc_real _, hS.cfc_real _⟩

end PositivityTheory.RgHe3
