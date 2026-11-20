import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.RightHalfWith

noncomputable section

open Metric

namespace PI.ZW

/- English proof (translation)
Establish `hR : 0 ≤ R` using `dist_nonneg.trans (Metric.mem_closedBall.1 hz)`. Use `hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected (Metric.mem_closedBall_self hR) hz ?_` and prove the remaining obligations. Rewrite using `[analyticOrderAt_eq_zero.2 (Or.inr hfc)]`. Conclude with `ENat.zero_ne_top`.
-/
lemma order_ne_top_of_ball {f : ℂ → ℂ} {c z : ℂ} {R : ℝ} (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hfc : f c ≠ 0) (hz : z ∈ closedBall c R) : analyticOrderAt f z ≠ ⊤ := by
  have hR : 0 ≤ R := dist_nonneg.trans (Metric.mem_closedBall.1 hz)
  refine hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected
    (Metric.mem_closedBall_self hR) hz ?_
  rw [analyticOrderAt_eq_zero.2 (Or.inr hfc)]
  exact ENat.zero_ne_top

/- English proof (translation)
Establish `hzR : z ∈ closedBall c R` using `closedBall_subset_closedBall hrR hz`. Establish `hm : MeromorphicOn f (closedBall c r)` using `(hf.mono (closedBall_subset_closedBall hrR)).meromorphicOn`. Establish `hne` using `order_ne_top_of_ball hf hfc hzR`. Rewrite using `[MeromorphicOn.divisor_apply hm hz, (hf z hzR).meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hne]`. Simplify using the standard rewrite rules.
-/
lemma divisor_eq_order {f : ℂ → ℂ} {c z : ℂ} {r R : ℝ} (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hfc : f c ≠ 0) (hrR : r ≤ R) (hz : z ∈ closedBall c r) :
    MeromorphicOn.divisor f (closedBall c r) z = (analyticOrderNatAt f z : ℤ) := by
  have hzR : z ∈ closedBall c R := closedBall_subset_closedBall hrR hz
  have hm : MeromorphicOn f (closedBall c r) := (hf.mono (closedBall_subset_closedBall hrR)).meromorphicOn
  have hne := order_ne_top_of_ball hf hfc hzR
  rw [MeromorphicOn.divisor_apply hm hz, (hf z hzR).meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hne]
  simp

/- English proof (translation)
Introduce `f c M hf hfc hM1 hbd S hS`. Establish `hR : |(19 / 10 : ℝ)| = 19 / 10` using `abs_of_pos (by norm_num)`. Establish `hf' : AnalyticOnNhd ℂ f (closedBall c |(19 / 10 : ℝ)|)` using `by rw [hR]; exact hf`. Establish `hDnn : 0 ≤ MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)` using `MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf'`. Establish `hfin : (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).support.Finite` using `(MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).finiteSupport (isCompact_closedBall _ _)`.

Establish `hSD : ∀ u ∈ S, MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) u = (analyticOrderNatAt f u : ℤ) ∧ 1 ≤ analyticOrderNatAt f u ∧ 0 < ‖c - u‖ ∧ ‖c - u‖ ≤ 37 / 20`. Introduce `u hu`. Take `⟨hub, hfu⟩` from `hS hu`. Establish `hub' : u ∈ closedBall c (19 / 10)` using `closedBall_subset_closedBall (by norm_num) hub`. Establish `hdiv` using `divisor_eq_order hf hfc le_rfl hub'`.

Establish `hne` using `order_ne_top_of_ball hf hfc hub'`. Use `⟨by rw [hR]; exact hdiv, ?_, ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h0 push_neg at h0`. Establish `h00 : analyticOrderNatAt f u = 0` using `by omega`. Establish `hord : analyticOrderAt f u = 0` using `by rw [← Nat.cast_analyticOrderNatAt hne, h00]; rfl`.

Break down `analyticOrderAt_eq_zero.1 hord with h | h` into its components or cases. Conclude with `h (hf u hub')`. Conclude with `h hfu`. Establish `: u ≠ c` using `by rintro rfl; exact hfc hfu`. Conclude with `norm_pos_iff.2 (sub_ne_zero.2 this.symm)`.

Rewrite using `[norm_sub_rev, ← dist_eq_norm]`. Conclude with `mem_closedBall.1 hub`. Establish `hSsub : S ⊆ (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).support`. Introduce `u hu`. Take `⟨h1, h2, -, -⟩` from `hSD u hu`.

Simplify using `only [Function.mem_support, h1]`. Conclude with `(by omega : analyticOrderNatAt f u ≠ 0)` after adjusting the coercions. Establish `hSfin : S.Finite` using `hfin.subset hSsub`. Use `⟨hSfin, ?_⟩` and prove the remaining obligations. Establish `hJ` using `AnalyticOnNhd.circleAverage_log_norm (c := c) (R := 19 / 10) (by norm_num) hf' hfc`.

Establish `hup : Real.circleAverage (fun x => Real.log ‖f x‖) c (19 / 10) ≤ Real.log M`. Apply `Real.circleAverage_mono_on_of_le_circle` to reduce the goal to its premises. Conclude with `MeromorphicOn.circleIntegrable_log_norm (hf'.mono sphere_subset_closedBall).meromorphicOn`. Introduce `x hx`. Rewrite `hx` using `[hR]`.

Distinguish the cases in `h0 : f x = 0`. Rewrite using `[h0, norm_zero, Real.log_zero]`. Conclude with `Real.log_nonneg hM1`. Conclude with `Real.log_le_log (norm_pos_iff.2 h0) (hbd x hx)`. Use `set g : ℂ → ℝ := fun u => (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) u : ℝ) * Real.log (19 / 10 * ‖c - u‖⁻¹) with hg`.

Establish `hgnn : ∀ u, 0 ≤ g u`. Introduce `u`. Distinguish the cases in `hu : u ∈ (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).support`. Establish `hdu : (0 : ℝ) ≤ (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) u : ℝ)`. Conclude with `hDnn u` after adjusting the coercions.

Establish `hin` using `(MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).supportWithinDomain hu`. Rewrite `hin` using `[hR]`. Establish `hcu : ‖c - u‖ ≤ 19 / 10` using `by rw [norm_sub_rev, ← dist_eq_norm]; exact mem_closedBall.1 hin`. Apply `mul_nonneg hdu` to reduce the goal to its premises. Break down `(norm_nonneg (c - u)).eq_or_lt with h0 | h0` into its components or cases.

Rewrite using `[← h0, inv_zero, mul_zero, Real.log_zero]`. Apply `Real.log_nonneg` to reduce the goal to its premises. Rewrite using `[← div_eq_mul_inv, le_div_iff₀ h0]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [Function.mem_support, not_not] at hu`.

Simplify using `[hg, hu]`. Establish `hgsupp : Function.support g ⊆ hfin.toFinset`. Introduce `u hu`. Simplify using `only [Set.Finite.coe_toFinset, Function.mem_support]`. Introduce `h0`.

Apply `hu` to reduce the goal to its premises. Simplify using `[hg, h0]`. Establish `hfs : ∑ᶠ u, g u = ∑ u ∈ hfin.toFinset, g u` using `finsum_eq_sum_of_support_subset g hgsupp`. Establish `hsub2 : hSfin.toFinset ⊆ hfin.toFinset`. Introduce `u hu`.

Simplify using `only [Set.Finite.mem_toFinset] at hu ⊢`. Conclude with `hSsub hu`. Establish `hlow : ∑ u ∈ hSfin.toFinset, g u ≤ ∑ u ∈ hfin.toFinset, g u` using `Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun u _ _ => hgnn u`. Establish `hLpos : 0 < Real.log ((19 / 10) / (37 / 20))` using `Real.log_pos (by norm_num)`. Establish `hterm : ∀ u ∈ hSfin.toFinset, (analyticOrderNatAt f u : ℝ) * Real.log ((19 / 10) / (37 / 20)) ≤ g u`.

Introduce `u hu`. Rewrite `hu` using `[Set.Finite.mem_toFinset]`. Take `⟨h1, h2, h3, h4⟩` from `hSD u hu`. Simplify using `only [hg, h1]`. Use `push_cast`.

Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Apply `Real.log_le_log (by norm_num)` to reduce the goal to its premises. Rewrite using `[← div_eq_mul_inv]`. Conclude with `div_le_div_of_nonneg_left (by norm_num) h3 h4`. Establish `hfc0 : 0 < ‖f c‖` using `norm_pos_iff.2 hfc`.

Establish `hM0 : 0 < M` using `by linarith`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hSfin, le_div_iff₀ hLpos, Finset.sum_mul, Real.log_div hM0.ne' hfc0.ne']`. Establish `hsum` using `Finset.sum_le_sum hterm`. Establish `hJ' : ∑ᶠ u, g u = Real.circleAverage (fun x => Real.log ‖f x‖) c (19 / 10) - Real.log ‖f c‖`. Rewrite using `[hJ]`.

Simplify using `only [hg]`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem jensenCount : JensenCount := by
  intro f c M hf hfc hM1 hbd S hS
  have hR : |(19 / 10 : ℝ)| = 19 / 10 := abs_of_pos (by norm_num)
  have hf' : AnalyticOnNhd ℂ f (closedBall c |(19 / 10 : ℝ)|) := by rw [hR]; exact hf
  have hDnn : 0 ≤ MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf'
  have hfin : (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).support.Finite :=
    (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).finiteSupport (isCompact_closedBall _ _)
  have hSD : ∀ u ∈ S, MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) u =
      (analyticOrderNatAt f u : ℤ) ∧ 1 ≤ analyticOrderNatAt f u ∧ 0 < ‖c - u‖ ∧ ‖c - u‖ ≤ 37 / 20 := by
    intro u hu
    obtain ⟨hub, hfu⟩ := hS hu
    have hub' : u ∈ closedBall c (19 / 10) := closedBall_subset_closedBall (by norm_num) hub
    have hdiv := divisor_eq_order hf hfc le_rfl hub'
    have hne := order_ne_top_of_ball hf hfc hub'
    refine ⟨by rw [hR]; exact hdiv, ?_, ?_, ?_⟩
    · by_contra h0
      push_neg at h0
      have h00 : analyticOrderNatAt f u = 0 := by omega
      have hord : analyticOrderAt f u = 0 := by rw [← Nat.cast_analyticOrderNatAt hne, h00]; rfl
      rcases analyticOrderAt_eq_zero.1 hord with h | h
      · exact h (hf u hub')
      · exact h hfu
    · have : u ≠ c := by rintro rfl; exact hfc hfu
      exact norm_pos_iff.2 (sub_ne_zero.2 this.symm)
    · rw [norm_sub_rev, ← dist_eq_norm]; exact mem_closedBall.1 hub
  have hSsub : S ⊆ (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).support := by
    intro u hu
    obtain ⟨h1, h2, -, -⟩ := hSD u hu
    simp only [Function.mem_support, h1]
    exact_mod_cast (by omega : analyticOrderNatAt f u ≠ 0)
  have hSfin : S.Finite := hfin.subset hSsub
  refine ⟨hSfin, ?_⟩
  have hJ := AnalyticOnNhd.circleAverage_log_norm (c := c) (R := 19 / 10) (by norm_num) hf' hfc
  have hup : Real.circleAverage (fun x => Real.log ‖f x‖) c (19 / 10) ≤ Real.log M := by
    apply Real.circleAverage_mono_on_of_le_circle
    · exact MeromorphicOn.circleIntegrable_log_norm (hf'.mono sphere_subset_closedBall).meromorphicOn
    · intro x hx
      rw [hR] at hx
      by_cases h0 : f x = 0
      · rw [h0, norm_zero, Real.log_zero]; exact Real.log_nonneg hM1
      · exact Real.log_le_log (norm_pos_iff.2 h0) (hbd x hx)
  set g : ℂ → ℝ := fun u => (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) u : ℝ) *
    Real.log (19 / 10 * ‖c - u‖⁻¹) with hg
  have hgnn : ∀ u, 0 ≤ g u := by
    intro u
    by_cases hu : u ∈ (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).support
    · have hdu : (0 : ℝ) ≤ (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) u : ℝ) := by
        exact_mod_cast hDnn u
      have hin := (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).supportWithinDomain hu
      rw [hR] at hin
      have hcu : ‖c - u‖ ≤ 19 / 10 := by rw [norm_sub_rev, ← dist_eq_norm]; exact mem_closedBall.1 hin
      apply mul_nonneg hdu
      rcases (norm_nonneg (c - u)).eq_or_lt with h0 | h0
      · rw [← h0, inv_zero, mul_zero, Real.log_zero]
      · apply Real.log_nonneg
        rw [← div_eq_mul_inv, le_div_iff₀ h0]; linarith
    · simp only [Function.mem_support, not_not] at hu
      simp [hg, hu]
  have hgsupp : Function.support g ⊆ hfin.toFinset := by
    intro u hu
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    intro h0
    apply hu
    simp [hg, h0]
  have hfs : ∑ᶠ u, g u = ∑ u ∈ hfin.toFinset, g u := finsum_eq_sum_of_support_subset g hgsupp
  have hsub2 : hSfin.toFinset ⊆ hfin.toFinset := by
    intro u hu
    simp only [Set.Finite.mem_toFinset] at hu ⊢
    exact hSsub hu
  have hlow : ∑ u ∈ hSfin.toFinset, g u ≤ ∑ u ∈ hfin.toFinset, g u :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun u _ _ => hgnn u
  have hLpos : 0 < Real.log ((19 / 10) / (37 / 20)) := Real.log_pos (by norm_num)
  have hterm : ∀ u ∈ hSfin.toFinset, (analyticOrderNatAt f u : ℝ) * Real.log ((19 / 10) / (37 / 20)) ≤ g u := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu
    obtain ⟨h1, h2, h3, h4⟩ := hSD u hu
    simp only [hg, h1]
    push_cast
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.log_le_log (by norm_num)
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by norm_num) h3 h4
  have hfc0 : 0 < ‖f c‖ := norm_pos_iff.2 hfc
  have hM0 : 0 < M := by linarith
  rw [finsum_mem_eq_finite_toFinset_sum _ hSfin, le_div_iff₀ hLpos, Finset.sum_mul,
    Real.log_div hM0.ne' hfc0.ne']
  have hsum := Finset.sum_le_sum hterm
  have hJ' : ∑ᶠ u, g u = Real.circleAverage (fun x => Real.log ‖f x‖) c (19 / 10) - Real.log ‖f c‖ := by
    rw [hJ]; simp only [hg]; ring
  linarith

end PI.ZW
