import Development.WeilBound.CoreStatements.CentralCharts.PshAt0

noncomputable section

namespace AnalyticReference.An.H

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar Filter Topology

variable {n a : ℕ} {f g : (Fin n → ℂ) → ℝ}

/- English proof (translation)
Unfold `logR`. Establish `hs : 0 ≤ ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0`. Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `i _`. Use `split_ifs with hi`.

Apply `Real.log_nonneg` to reduce the goal to its premises. Establish `h1 : ‖t i‖ ≤ ‖t‖` using `norm_le_pi_norm t i`. Establish `h2 : 0 < ‖t i‖` using `norm_pos_iff.mpr (h i hi)`. Rewrite using `[le_div_iff₀ (by positivity), one_mul]`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `le_rfl`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exp_le_logR {t : Fin n → ℂ} (ht : ‖t‖ < 1) (h : ∀ i : Fin n, (i : ℕ) < a → t i ≠ 0) :
    Real.exp 1 ≤ logR a t := by
  unfold logR
  have hs : 0 ≤ ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0 := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs with hi
    · apply Real.log_nonneg
      have h1 : ‖t i‖ ≤ ‖t‖ := norm_le_pi_norm t i
      have h2 : 0 < ‖t i‖ := norm_pos_iff.mpr (h i hi)
      rw [le_div_iff₀ (by positivity), one_mul]
      nlinarith
    · exact le_rfl
  linarith

/- English proof (translation)
Use `exp_le_logR ht h` as an intermediate fact. Use `Real.add_one_le_exp (1 : ℝ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_logR {t : Fin n → ℂ} (ht : ‖t‖ < 1) (h : ∀ i : Fin n, (i : ℕ) < a → t i ≠ 0) : 1 ≤ logR a t := by
  have := exp_le_logR ht h
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem one_le_log_logR {t : Fin n → ℂ} (ht : ‖t‖ < 1) (h : ∀ i : Fin n, (i : ℕ) < a → t i ≠ 0) :
    1 ≤ Real.log (logR a t) := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (logR a t) := Real.log_le_log (Real.exp_pos 1) (exp_le_logR ht h)

/- English proof (translation)
Use `⟨min ε 1, max (max C₁ C₂) e, lt_min hε one_pos, min_le_right _ _, le_max_of_le_left (le_max_of_le_left h1), ?_⟩` and prove the remaining obligations. Introduce `t ht hoff`. Establish `ht1 : ‖t‖ < 1` using `lt_of_lt_of_le ht (min_le_right _ _)`. Take `⟨hc, hb1, hb2⟩` from `h t (lt_of_lt_of_le ht (min_le_left _ _)) ht1 hoff`. Establish `hL` using `one_le_logR ht1 hoff`.

Establish `hLL` using `one_le_log_logR ht1 hoff`. Establish `hC1 : C₁ ≤ max (max C₁ C₂) e` using `le_max_of_le_left (le_max_left _ _)`. Establish `hC2 : C₂ ≤ max (max C₁ C₂) e` using `le_max_of_le_left (le_max_right _ _)`. Establish `hCe : e ≤ max (max C₁ C₂) e` using `le_max_right _ _`. Use `⟨hc, ?_, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le` to reduce the goal to its premises. Conclude with `mul_le_mul hC2 (Real.rpow_le_rpow_of_exponent_le hL hCe) (Real.rpow_nonneg (by linarith) _) (by linarith)`.
-/
theorem tame_of {ε C₁ C₂ e : ℝ} (hε : 0 < ε) (h1 : 0 ≤ C₁) (h2 : 0 ≤ C₂) (he : 0 ≤ e)
    (h : ∀ t : Fin n → ℂ, ‖t‖ < ε → ‖t‖ < 1 → (∀ i : Fin n, (i : ℕ) < a → t i ≠ 0) →
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f t ∧ |f t| ≤ C₁ * Real.log (logR a t) ∧
        ‖fderiv ℝ f t‖ ≤ C₂ * logR a t ^ e * Real.exp (logR a t / 2)) : Tame a f := by
  refine ⟨min ε 1, max (max C₁ C₂) e, lt_min hε one_pos, min_le_right _ _, le_max_of_le_left (le_max_of_le_left h1), ?_⟩
  intro t ht hoff
  have ht1 : ‖t‖ < 1 := lt_of_lt_of_le ht (min_le_right _ _)
  obtain ⟨hc, hb1, hb2⟩ := h t (lt_of_lt_of_le ht (min_le_left _ _)) ht1 hoff
  have hL := one_le_logR ht1 hoff
  have hLL := one_le_log_logR ht1 hoff
  have hC1 : C₁ ≤ max (max C₁ C₂) e := le_max_of_le_left (le_max_left _ _)
  have hC2 : C₂ ≤ max (max C₁ C₂) e := le_max_of_le_left (le_max_right _ _)
  have hCe : e ≤ max (max C₁ C₂) e := le_max_right _ _
  refine ⟨hc, ?_, ?_⟩
  · calc |f t| ≤ C₁ * Real.log (logR a t) := hb1
      _ ≤ max (max C₁ C₂) e * Real.log (logR a t) := mul_le_mul_of_nonneg_right hC1 (by linarith)
  · calc ‖fderiv ℝ f t‖ ≤ C₂ * logR a t ^ e * Real.exp (logR a t / 2) := hb2
      _ ≤ max (max C₁ C₂) e * logR a t ^ max (max C₁ C₂) e * Real.exp (logR a t / 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul hC2 (Real.rpow_le_rpow_of_exponent_le hL hCe) (Real.rpow_nonneg (by linarith) _) (by linarith)

/- English proof (translation)
Take `⟨ε₁, C₁, hε₁, -, hC₁, hf⟩` from `hf`. Take `⟨ε₂, C₂, hε₂, -, hC₂, hg⟩` from `hg`. Apply `tame_of (ε := min ε₁ ε₂) (C₁ := C₁ + C₂) (C₂ := C₁ + C₂) (e := C₁ + C₂) (lt_min hε₁ hε₂) (by linarith) (by linarith) (by linarith)` to reduce the goal to its premises. Introduce `t ht ht1 hoff`. Use `beta_reduce`.

Take `⟨hfc, hf1, hf2⟩` from `hf t (lt_of_lt_of_le ht (min_le_left _ _)) hoff`. Take `⟨hgc, hg1, hg2⟩` from `hg t (lt_of_lt_of_le ht (min_le_right _ _)) hoff`. Establish `hL` using `one_le_logR ht1 hoff`. Establish `hE` using `(Real.exp_pos (logR a t / 2)).le`. Establish `p1 : logR a t ^ C₁ ≤ logR a t ^ (C₁ + C₂)` using `Real.rpow_le_rpow_of_exponent_le hL (by linarith)`.

Establish `p2 : logR a t ^ C₂ ≤ logR a t ^ (C₁ + C₂)` using `Real.rpow_le_rpow_of_exponent_le hL (by linarith)`. Establish `hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0` using `by simp`. Use `⟨hfc.add hgc, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[fderiv_fun_add (hfc.differentiableAt hn) (hgc.differentiableAt hn)]`.

Combine the equalities or inequalities in the displayed calculation. Establish `a1 : C₁ * logR a t ^ C₁ ≤ C₁ * logR a t ^ (C₁ + C₂)` using `mul_le_mul_of_nonneg_left p1 hC₁`. Establish `a2 : C₂ * logR a t ^ C₂ ≤ C₂ * logR a t ^ (C₁ + C₂)` using `mul_le_mul_of_nonneg_left p2 hC₂`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem add (hf : Tame a f) (hg : Tame a g) : Tame a fun t => f t + g t := by
  obtain ⟨ε₁, C₁, hε₁, -, hC₁, hf⟩ := hf
  obtain ⟨ε₂, C₂, hε₂, -, hC₂, hg⟩ := hg
  apply tame_of (ε := min ε₁ ε₂) (C₁ := C₁ + C₂) (C₂ := C₁ + C₂) (e := C₁ + C₂) (lt_min hε₁ hε₂) (by linarith) (by linarith) (by linarith)
  intro t ht ht1 hoff
  beta_reduce
  obtain ⟨hfc, hf1, hf2⟩ := hf t (lt_of_lt_of_le ht (min_le_left _ _)) hoff
  obtain ⟨hgc, hg1, hg2⟩ := hg t (lt_of_lt_of_le ht (min_le_right _ _)) hoff
  have hL := one_le_logR ht1 hoff
  have hE := (Real.exp_pos (logR a t / 2)).le
  have p1 : logR a t ^ C₁ ≤ logR a t ^ (C₁ + C₂) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have p2 : logR a t ^ C₂ ≤ logR a t ^ (C₁ + C₂) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hfc.add hgc, ?_, ?_⟩
  · calc |f t + g t| ≤ |f t| + |g t| := abs_add_le _ _
      _ ≤ _ := by linarith
  · rw [fderiv_fun_add (hfc.differentiableAt hn) (hgc.differentiableAt hn)]
    calc ‖fderiv ℝ f t + fderiv ℝ g t‖ ≤ ‖fderiv ℝ f t‖ + ‖fderiv ℝ g t‖ := norm_add_le _ _
      _ ≤ C₁ * logR a t ^ C₁ * Real.exp (logR a t / 2) + C₂ * logR a t ^ C₂ * Real.exp (logR a t / 2) := add_le_add hf2 hg2
      _ ≤ (C₁ + C₂) * logR a t ^ (C₁ + C₂) * Real.exp (logR a t / 2) := by
        have a1 : C₁ * logR a t ^ C₁ ≤ C₁ * logR a t ^ (C₁ + C₂) := mul_le_mul_of_nonneg_left p1 hC₁
        have a2 : C₂ * logR a t ^ C₂ ≤ C₂ * logR a t ^ (C₁ + C₂) := mul_le_mul_of_nonneg_left p2 hC₂
        nlinarith

/- English proof (translation)
Take `⟨ε, C, hε, -, hC, h⟩` from `hf`. Use `tame_of (C₁ := |c| * C) (C₂ := |c| * C) (e := C) hε (by positivity) (by positivity) hC fun t ht _ hi => ?_` and prove the remaining obligations. Take `⟨a1, a2, a3⟩` from `h t ht hi`. Use `⟨contDiffAt_const.mul a1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[abs_mul, mul_assoc]`.

Use `gcongr`. Rewrite using `[fderiv_const_mul (a1.differentiableAt (by simp)), norm_smul, Real.norm_eq_abs, mul_assoc, mul_assoc, ← mul_assoc C] gcongr`.
-/
theorem const_mul (c : ℝ) (hf : Tame a f) : Tame a fun t => c * f t := by
  obtain ⟨ε, C, hε, -, hC, h⟩ := hf
  refine tame_of (C₁ := |c| * C) (C₂ := |c| * C) (e := C) hε (by positivity) (by positivity) hC
    fun t ht _ hi => ?_
  obtain ⟨a1, a2, a3⟩ := h t ht hi
  refine ⟨contDiffAt_const.mul a1, ?_, ?_⟩
  · rw [abs_mul, mul_assoc]; gcongr
  · rw [fderiv_const_mul (a1.differentiableAt (by simp)), norm_smul, Real.norm_eq_abs, mul_assoc, mul_assoc,
      ← mul_assoc C]
    gcongr

/- English proof (translation)
Use `⟨1, 0, one_pos, le_rfl, le_rfl, fun t _ _ => ⟨contDiffAt_const, by simp, by simp⟩⟩` and prove the remaining obligations.
-/
theorem tame_zero : Tame a fun _ : Fin n → ℂ => (0 : ℝ) := by
  refine ⟨1, 0, one_pos, le_rfl, le_rfl, fun t _ _ => ⟨contDiffAt_const, by simp, by simp⟩⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using tame_zero`. Consider the case `insert i s hi ih`. Simplify using `only [Finset.sum_insert hi]`. Conclude with `add (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))`.
-/
theorem sum {ι : Type} (s : Finset ι) {F : ι → (Fin n → ℂ) → ℝ} (h : ∀ i ∈ s, Tame a (F i)) :
    Tame a fun t => ∑ i ∈ s, F i t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tame_zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact add (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Establish `hs : {t : Fin n → ℂ | ∀ i : Fin n, (i : ℕ) < a → t i ≠ 0} = ⋂ i : Fin n, {t | (i : ℕ) < a → t i ≠ 0}`. Use `ext`. Simplify using the standard rewrite rules. Rewrite using `[hs]`. Apply `isOpen_iInter_of_finite` to reduce the goal to its premises.

Introduce `i`. Distinguish the cases in `hi : (i : ℕ) < a`. Simplify using `only [hi, true_implies]`. Conclude with `isOpen_ne_fun (continuous_apply i) continuous_const`. Simplify using `[hi]`.
-/
theorem isOpen_off (n a : ℕ) : IsOpen {t : Fin n → ℂ | ∀ i : Fin n, (i : ℕ) < a → t i ≠ 0} := by
  have hs : {t : Fin n → ℂ | ∀ i : Fin n, (i : ℕ) < a → t i ≠ 0} = ⋂ i : Fin n, {t | (i : ℕ) < a → t i ≠ 0} := by
    ext
    simp
  rw [hs]
  apply isOpen_iInter_of_finite
  intro i
  by_cases hi : (i : ℕ) < a
  · simp only [hi, true_implies]
    exact isOpen_ne_fun (continuous_apply i) continuous_const
  · simp [hi]

/- English proof (translation)
Take `⟨ε, C, hε, hε1, hC, hf⟩` from `hf`. Take `⟨δ, hδ, hδh⟩` from `Metric.eventually_nhds_iff.mp h`. Use `⟨min ε δ, C, lt_min hε hδ, (min_le_left _ _).trans hε1, hC, ?_⟩` and prove the remaining obligations. Introduce `t ht hoff`. Take `⟨hfc, hf1, hf2⟩` from `hf t (lt_of_lt_of_le ht (min_le_left _ _)) hoff`.

Establish `hev : g =ᶠ[𝓝 t] f`. Establish `hU : IsOpen (Metric.ball (0 : Fin n → ℂ) δ ∩ {t : Fin n → ℂ | ∀ i : Fin n, (i : ℕ) < a → t i ≠ 0})` using `Metric.isOpen_ball.inter (isOpen_off n a)`. Establish `htU : t ∈ Metric.ball (0 : Fin n → ℂ) δ ∩ {t : Fin n → ℂ | ∀ i : Fin n, (i : ℕ) < a → t i ≠ 0}`. Use `⟨?_, hoff⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_ball, dist_zero_right]`.

Conclude with `lt_of_lt_of_le ht (min_le_right _ _)`. Use `filter_upwards [hU.mem_nhds htU] with y hy`. Conclude with `hδh hy.1 hy.2`. Use `⟨hfc.congr_of_eventuallyEq hev, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hev.eq_of_nhds]`.

Conclude with `hf1`. Rewrite using `[hev.fderiv_eq]`. Conclude with `hf2`.
-/
theorem congr (hf : Tame a f) (h : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), (∀ i : Fin n, (i : ℕ) < a → t i ≠ 0) → g t = f t) :
    Tame a g := by
  obtain ⟨ε, C, hε, hε1, hC, hf⟩ := hf
  obtain ⟨δ, hδ, hδh⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨min ε δ, C, lt_min hε hδ, (min_le_left _ _).trans hε1, hC, ?_⟩
  intro t ht hoff
  obtain ⟨hfc, hf1, hf2⟩ := hf t (lt_of_lt_of_le ht (min_le_left _ _)) hoff
  have hev : g =ᶠ[𝓝 t] f := by
    have hU : IsOpen (Metric.ball (0 : Fin n → ℂ) δ ∩ {t : Fin n → ℂ | ∀ i : Fin n, (i : ℕ) < a → t i ≠ 0}) :=
      Metric.isOpen_ball.inter (isOpen_off n a)
    have htU : t ∈ Metric.ball (0 : Fin n → ℂ) δ ∩ {t : Fin n → ℂ | ∀ i : Fin n, (i : ℕ) < a → t i ≠ 0} := by
      refine ⟨?_, hoff⟩
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_lt_of_le ht (min_le_right _ _)
    filter_upwards [hU.mem_nhds htU] with y hy
    exact hδh hy.1 hy.2
  refine ⟨hfc.congr_of_eventuallyEq hev, ?_, ?_⟩
  · rw [hev.eq_of_nhds]
    exact hf1
  · rw [hev.fderiv_eq]
    exact hf2

/- English proof (translation)
Establish `h0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f 0` using `hf.self_of_nhds`. Establish `hc1 : ContinuousAt f 0` using `h0.continuousAt`. Establish `hc2 : ContinuousAt (fderiv ℝ f) 0` using `(h0.fderiv_right (m := 0) (by simp)).continuousAt`. Establish `e1 : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), |f t| < |f 0| + 1` using `(continuous_abs.continuousAt.comp hc1).eventually (gt_mem_nhds (lt_add_one _))`. Establish `e2 : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), ‖fderiv ℝ f t‖ < ‖fderiv ℝ f 0‖ + 1` using `hc2.norm.eventually (gt_mem_nhds (lt_add_one _))`.

Take `⟨δ, hδ, hδh⟩` from `Metric.eventually_nhds_iff.mp (hf.and (e1.and e2))`. Establish `hM0 : 0 ≤ max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1)` using `le_max_of_le_left (by positivity)`. Apply `tame_of (ε := δ) (C₁ := max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1)) (C₂ := max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1)) (e := max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1)) hδ hM0 hM0 hM0` to reduce the goal to its premises. Introduce `t ht ht1 hoff`. Take `⟨hct, hb1, hb2⟩` from `hδh (by rwa [dist_zero_right])`.

Establish `hL` using `one_le_logR ht1 hoff`. Establish `hLL` using `one_le_log_logR ht1 hoff`. Use `⟨hct, ?_, ?_⟩` and prove the remaining obligations. Establish `: |f t| ≤ max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1)` using `hb1.le.trans (le_max_left _ _)`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hb : ‖fderiv ℝ f t‖ ≤ max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1)` using `hb2.le.trans (le_max_right _ _)`. Establish `hp : 1 ≤ logR a t ^ max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1)` using `Real.one_le_rpow hL hM0`. Establish `he : 1 ≤ Real.exp (logR a t / 2)` using `Real.one_le_exp (by linarith)`. Establish `h1 : 1 ≤ logR a t ^ max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1) * Real.exp (logR a t / 2)` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tame_of_smooth (a : ℕ) (hf : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f t) :
    Tame a f := by
  have h0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f 0 := hf.self_of_nhds
  have hc1 : ContinuousAt f 0 := h0.continuousAt
  have hc2 : ContinuousAt (fderiv ℝ f) 0 := (h0.fderiv_right (m := 0) (by simp)).continuousAt
  have e1 : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), |f t| < |f 0| + 1 :=
    (continuous_abs.continuousAt.comp hc1).eventually (gt_mem_nhds (lt_add_one _))
  have e2 : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), ‖fderiv ℝ f t‖ < ‖fderiv ℝ f 0‖ + 1 :=
    hc2.norm.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨δ, hδ, hδh⟩ := Metric.eventually_nhds_iff.mp (hf.and (e1.and e2))
  have hM0 : 0 ≤ max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1) := le_max_of_le_left (by positivity)
  apply tame_of (ε := δ) (C₁ := max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1)) (C₂ := max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1))
    (e := max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1)) hδ hM0 hM0 hM0
  intro t ht ht1 hoff
  obtain ⟨hct, hb1, hb2⟩ := hδh (by rwa [dist_zero_right])
  have hL := one_le_logR ht1 hoff
  have hLL := one_le_log_logR ht1 hoff
  refine ⟨hct, ?_, ?_⟩
  · have : |f t| ≤ max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1) := hb1.le.trans (le_max_left _ _)
    nlinarith
  · have hb : ‖fderiv ℝ f t‖ ≤ max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1) := hb2.le.trans (le_max_right _ _)
    have hp : 1 ≤ logR a t ^ max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1) := Real.one_le_rpow hL hM0
    have he : 1 ≤ Real.exp (logR a t / 2) := Real.one_le_exp (by linarith)
    have h1 : 1 ≤ logR a t ^ max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1) * Real.exp (logR a t / 2) := by nlinarith
    calc ‖fderiv ℝ f t‖ ≤ max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1) := hb
      _ ≤ max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1) * (logR a t ^ max (|f 0| + 1) (‖fderiv ℝ f 0‖ + 1) * Real.exp (logR a t / 2)) :=
        le_mul_of_one_le_right hM0 h1
      _ = _ := by ring

/- English proof (translation)
Establish `hF' : ContDiffAt ℝ m F t` using `(hF.contDiffAt).restrict_scalars ℝ`. Establish `hn : ContDiffAt ℝ m (fun t => ‖F t‖) t` using `(contDiffAt_norm ℝ h0).comp t hF'`. Conclude with `hn.log (norm_ne_zero_iff.mpr h0)`.
-/
theorem contDiffAt_log_norm {F : (Fin n → ℂ) → ℂ} {t : Fin n → ℂ} (hF : AnalyticAt ℂ F t) (h0 : F t ≠ 0)
    {m : WithTop ℕ∞} : ContDiffAt ℝ m (fun t => Real.log ‖F t‖) t := by
  have hF' : ContDiffAt ℝ m F t := (hF.contDiffAt).restrict_scalars ℝ
  have hn : ContDiffAt ℝ m (fun t => ‖F t‖) t := (contDiffAt_norm ℝ h0).comp t hF'
  exact hn.log (norm_ne_zero_iff.mpr h0)

/- English proof (translation)
Use `tame_of_smooth a ?_` and prove the remaining obligations. Use `filter_upwards [hF.eventually_analyticAt, hF.continuousAt.eventually_ne h0] with t h1 h2`. Conclude with `contDiffAt_log_norm h1 h2`.
-/
theorem tame_log_norm (a : ℕ) {F : (Fin n → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 ≠ 0) :
    Tame a fun t => Real.log ‖F t‖ := by
  refine tame_of_smooth a ?_
  filter_upwards [hF.eventually_analyticAt, hF.continuousAt.eventually_ne h0] with t h1 h2
  exact contDiffAt_log_norm h1 h2

/- English proof (translation)
Establish `ef : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), DifferentiableAt ℝ f t` using `(hf.eventually (by simp)).mono fun t ht => ht.differentiableAt (by simp)`. Establish `eg : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), DifferentiableAt ℝ g t` using `(hg.eventually (by simp)).mono fun t ht => ht.differentiableAt (by simp)`. Establish `hEq : fderiv ℝ (fun t => f t + g t) =ᶠ[𝓝 0] fun t => fderiv ℝ f t + fderiv ℝ g t` using `by filter_upwards [ef, eg] with t h1 h2`. Conclude with `fderiv_fun_add h1 h2`. Rewrite using `[hEq.fderiv_eq]`.

Conclude with `fderiv_fun_add ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)) ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))`.
-/
private theorem padd_lemma {f g : (Fin n → ℂ) → ℝ} (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 2 g 0) :
    fderiv ℝ (fderiv ℝ (fun t => f t + g t)) 0 = fderiv ℝ (fderiv ℝ f) 0 + fderiv ℝ (fderiv ℝ g) 0 := by
  have ef : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), DifferentiableAt ℝ f t :=
    (hf.eventually (by simp)).mono fun t ht => ht.differentiableAt (by simp)
  have eg : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), DifferentiableAt ℝ g t :=
    (hg.eventually (by simp)).mono fun t ht => ht.differentiableAt (by simp)
  have hEq : fderiv ℝ (fun t => f t + g t) =ᶠ[𝓝 0] fun t => fderiv ℝ f t + fderiv ℝ g t := by
    filter_upwards [ef, eg] with t h1 h2
    exact fderiv_fun_add h1 h2
  rw [hEq.fderiv_eq]
  exact fderiv_fun_add ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

/- English proof (translation)
Use `⟨hf.1.add hg.1, fun w => ?_⟩` and prove the remaining obligations. Establish `h` using `padd_lemma hf.1 hg.1`. Establish `e : levi (fun t => f t + g t) 0 w = levi f 0 w + levi g 0 w`. Unfold `levi`. Rewrite using `[h]`.

Simplify using `only [ContinuousLinearMap.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `add_nonneg (hf.2 w) (hg.2 w)`.
-/
theorem padd (hf : PshAt0 f) (hg : PshAt0 g) : PshAt0 fun t => f t + g t := by
  refine ⟨hf.1.add hg.1, fun w => ?_⟩
  have h := padd_lemma hf.1 hg.1
  have e : levi (fun t => f t + g t) 0 w = levi f 0 w + levi g 0 w := by
    unfold levi
    rw [h]
    simp only [ContinuousLinearMap.add_apply]
    ring
  rw [e]
  exact add_nonneg (hf.2 w) (hg.2 w)

/- English proof (translation)
Simplify using `[levi]`.
-/
theorem levi_const (d : ℝ) (z w : Fin n → ℂ) : levi (fun _ => d) z w = 0 := by
  simp [levi]

/- English proof (translation)
Assemble the required witnesses or components as `⟨contDiffAt_const, fun w => (levi_const d 0 w).ge⟩`.
-/
theorem pconst (d : ℝ) : PshAt0 fun _ : Fin n → ℂ => d := ⟨contDiffAt_const, fun w => (levi_const d 0 w).ge⟩

/- English proof (translation)
Establish `ef : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), DifferentiableAt ℝ f t` using `(hf.eventually (by simp)).mono fun t ht => ht.differentiableAt (by simp)`. Establish `hEq : fderiv ℝ (fun t => c * f t) =ᶠ[𝓝 0] fun t => c • fderiv ℝ f t` using `by filter_upwards [ef] with t h1`. Conclude with `fderiv_const_mul h1 c`. Rewrite using `[hEq.fderiv_eq]`. Conclude with `fderiv_const_smul ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)) c`.
-/
private theorem pconst_mul_lemma {f : (Fin n → ℂ) → ℝ} (c : ℝ) (hf : ContDiffAt ℝ 2 f 0) :
    fderiv ℝ (fderiv ℝ (fun t => c * f t)) 0 = c • fderiv ℝ (fderiv ℝ f) 0 := by
  have ef : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), DifferentiableAt ℝ f t :=
    (hf.eventually (by simp)).mono fun t ht => ht.differentiableAt (by simp)
  have hEq : fderiv ℝ (fun t => c * f t) =ᶠ[𝓝 0] fun t => c • fderiv ℝ f t := by
    filter_upwards [ef] with t h1
    exact fderiv_const_mul h1 c
  rw [hEq.fderiv_eq]
  exact fderiv_const_smul ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)) c

/- English proof (translation)
Use `⟨contDiffAt_const.mul hf.1, fun w => ?_⟩` and prove the remaining obligations. Establish `e : levi (fun t => c * f t) 0 w = c * levi f 0 w`. Unfold `levi`. Rewrite using `[pconst_mul_lemma c hf.1]`. Simplify using `only [ContinuousLinearMap.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_nonneg hc (hf.2 w)`.
-/
theorem pconst_mul {c : ℝ} (hc : 0 ≤ c) (hf : PshAt0 f) : PshAt0 fun t => c * f t := by
  refine ⟨contDiffAt_const.mul hf.1, fun w => ?_⟩
  have e : levi (fun t => c * f t) 0 w = c * levi f 0 w := by
    unfold levi
    rw [pconst_mul_lemma c hf.1]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [e]
  exact mul_nonneg hc (hf.2 w)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using pconst 0`. Consider the case `insert i s hi ih`. Simplify using `only [Finset.sum_insert hi]`. Conclude with `padd (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))`.
-/
theorem psum {ι : Type} (s : Finset ι) {F : ι → (Fin n → ℂ) → ℝ} (h : ∀ i ∈ s, PshAt0 (F i)) :
    PshAt0 fun t => ∑ i ∈ s, F i t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pconst 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact padd (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Use `⟨hf.1.congr_of_eventuallyEq h, fun w => ?_⟩` and prove the remaining obligations. Establish `e : fderiv ℝ (fderiv ℝ g) 0 = fderiv ℝ (fderiv ℝ f) 0` using `h.fderiv.fderiv_eq`. Establish `e2 : levi g 0 w = levi f 0 w`. Unfold `levi`. Rewrite using `[e]`.

Rewrite using `[e2]`. Conclude with `hf.2 w`.
-/
theorem pcongr (hf : PshAt0 f) (h : g =ᶠ[𝓝 0] f) : PshAt0 g := by
  refine ⟨hf.1.congr_of_eventuallyEq h, fun w => ?_⟩
  have e : fderiv ℝ (fderiv ℝ g) 0 = fderiv ℝ (fderiv ℝ f) 0 := h.fderiv.fderiv_eq
  have e2 : levi g 0 w = levi f 0 w := by
    unfold levi
    rw [e]
  rw [e2]
  exact hf.2 w

/- English proof (translation)
Establish `h1 : HasFDerivAt (fun t => (K t).re) (Complex.reCLM.comp ((fderiv ℂ K x).restrictScalars ℝ)) x` using `Complex.reCLM.hasFDerivAt.comp x (hK.hasFDerivAt.restrictScalars ℝ)`. Rewrite using `[h1.fderiv]`. Both sides reduce to the same expression.
-/
private theorem pre_lemma {K : (Fin n → ℂ) → ℂ} {x : Fin n → ℂ} (hK : DifferentiableAt ℂ K x) (v : Fin n → ℂ) :
    fderiv ℝ (fun t => (K t).re) x v = (fderiv ℂ K x v).re := by
  have h1 : HasFDerivAt (fun t => (K t).re) (Complex.reCLM.comp ((fderiv ℂ K x).restrictScalars ℝ)) x :=
    Complex.reCLM.hasFDerivAt.comp x (hK.hasFDerivAt.restrictScalars ℝ)
  rw [h1.fderiv]
  rfl

/- English proof (translation)
Rewrite using `[fderiv_clm_apply hc (differentiableAt_const u)]`. Simplify using the standard rewrite rules.
-/
private theorem pre_lemma_2 {𝕜 : Type} [RCLike 𝕜] {E F : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {c : E → E →L[𝕜] F} {x : E} (hc : DifferentiableAt 𝕜 c x) (u v : E) :
    fderiv 𝕜 (fun y => c y u) x v = fderiv 𝕜 c x v u := by
  rw [fderiv_clm_apply hc (differentiableAt_const u)]
  simp

/- English proof (translation)
Establish `hc : ContDiffAt ℝ 2 (fun t => (G t).re) 0` using `Complex.reCLM.contDiff.contDiffAt.comp 0 (hG.contDiffAt.restrict_scalars ℝ)`. Use `⟨hc, fun w => ?_⟩` and prove the remaining obligations. Establish `hev : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), AnalyticAt ℂ G t` using `hG.eventually_analyticAt`. Establish `hψd : DifferentiableAt ℝ (fderiv ℝ (fun t => (G t).re)) 0` using `(hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `hG' : AnalyticAt ℂ (fderiv ℂ G) 0` using `hG.fderiv`.

Establish `key : ∀ v u : Fin n → ℂ, fderiv ℝ (fderiv ℝ (fun t => (G t).re)) 0 v u = (fderiv ℂ (fderiv ℂ G) 0 v u).re`. Introduce `v u`. Rewrite using `[← pre_lemma_2 hψd u v]`. Establish `heq : (fun y => fderiv ℝ (fun t => (G t).re) y u) =ᶠ[𝓝 0] fun y => (fderiv ℂ G y u).re` using `by filter_upwards [hev] with y hy`. Conclude with `pre_lemma hy.differentiableAt u`.

Rewrite using `[heq.fderiv_eq]`. Establish `hKu : DifferentiableAt ℂ (fun y => fderiv ℂ G y u) 0` using `hG'.differentiableAt.clm_apply (differentiableAt_const u)`. Rewrite using `[pre_lemma hKu v, pre_lemma_2 hG'.differentiableAt u v]`. Unfold `levi`. Rewrite using `[key, key]`.

Establish `hI : fderiv ℂ (fderiv ℂ G) 0 (Complex.I • w) (Complex.I • w) = - fderiv ℂ (fderiv ℂ G) 0 w w`. Simplify using `only [map_smul, ContinuousLinearMap.smul_apply, smul_smul, Complex.I_mul_I, neg_smul, one_smul]`. Rewrite using `[hI, Complex.neg_re]`. Simplify using the standard rewrite rules.
-/
theorem pre {G : (Fin n → ℂ) → ℂ} (hG : AnalyticAt ℂ G 0) : PshAt0 fun t => (G t).re := by
  have hc : ContDiffAt ℝ 2 (fun t => (G t).re) 0 :=
    Complex.reCLM.contDiff.contDiffAt.comp 0 (hG.contDiffAt.restrict_scalars ℝ)
  refine ⟨hc, fun w => ?_⟩
  have hev : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), AnalyticAt ℂ G t := hG.eventually_analyticAt
  have hψd : DifferentiableAt ℝ (fderiv ℝ (fun t => (G t).re)) 0 :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG' : AnalyticAt ℂ (fderiv ℂ G) 0 := hG.fderiv
  have key : ∀ v u : Fin n → ℂ,
      fderiv ℝ (fderiv ℝ (fun t => (G t).re)) 0 v u = (fderiv ℂ (fderiv ℂ G) 0 v u).re := by
    intro v u
    rw [← pre_lemma_2 hψd u v]
    have heq : (fun y => fderiv ℝ (fun t => (G t).re) y u) =ᶠ[𝓝 0] fun y => (fderiv ℂ G y u).re := by
      filter_upwards [hev] with y hy
      exact pre_lemma hy.differentiableAt u
    rw [heq.fderiv_eq]
    have hKu : DifferentiableAt ℂ (fun y => fderiv ℂ G y u) 0 :=
      hG'.differentiableAt.clm_apply (differentiableAt_const u)
    rw [pre_lemma hKu v, pre_lemma_2 hG'.differentiableAt u v]
  unfold levi
  rw [key, key]
  have hI : fderiv ℂ (fderiv ℂ G) 0 (Complex.I • w) (Complex.I • w) = - fderiv ℂ (fderiv ℂ G) 0 w w := by
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  rw [hI, Complex.neg_re]
  simp

/- English proof (translation)
Establish `hdiv : AnalyticAt ℂ (fun t => F t / F 0) 0` using `hF.div analyticAt_const h0`. Establish `h1 : F 0 / F 0 ∈ Complex.slitPlane`. Rewrite using `[div_self h0]`. Conclude with `Complex.one_mem_slitPlane`. Establish `hK : AnalyticAt ℂ (fun t => (c : ℂ) * Complex.log (F t / F 0)) 0` using `analyticAt_const.mul (AnalyticAt.comp (g := Complex.log) (f := fun t => F t / F 0) (x := 0) (analyticAt_clog h1) hdiv)`.

Apply `pcongr (padd (pre hK) (pconst (c * Real.log ‖F 0‖ + d)))` to reduce the goal to its premises. Use `filter_upwards [hF.continuousAt.eventually_ne h0] with t ht`. Simplify using `only [Complex.re_ofReal_mul, Complex.log_re, norm_div]`. Rewrite using `[Real.log_div (norm_ne_zero_iff.mpr ht) (norm_ne_zero_iff.mpr h0)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem plog_norm (c d : ℝ) {F : (Fin n → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 ≠ 0) :
    PshAt0 fun t => c * Real.log ‖F t‖ + d := by
  have hdiv : AnalyticAt ℂ (fun t => F t / F 0) 0 := hF.div analyticAt_const h0
  have h1 : F 0 / F 0 ∈ Complex.slitPlane := by
    rw [div_self h0]
    exact Complex.one_mem_slitPlane
  have hK : AnalyticAt ℂ (fun t => (c : ℂ) * Complex.log (F t / F 0)) 0 :=
    analyticAt_const.mul (AnalyticAt.comp (g := Complex.log) (f := fun t => F t / F 0) (x := 0) (analyticAt_clog h1) hdiv)
  apply pcongr (padd (pre hK) (pconst (c * Real.log ‖F 0‖ + d)))
  filter_upwards [hF.continuousAt.eventually_ne h0] with t ht
  simp only [Complex.re_ofReal_mul, Complex.log_re, norm_div]
  rw [Real.log_div (norm_ne_zero_iff.mpr ht) (norm_ne_zero_iff.mpr h0)]
  ring

/- English proof (translation)
Use `set ψ := fderiv ℝ f with hψe`. Use `set B := fderiv ℝ ψ 0 with hB`. Establish `hψd : DifferentiableAt ℝ ψ 0` using `(hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `hψ0 : ψ 0 = 0` using `hm.fderiv_eq_zero`. Assume the negation of the conclusion as `hq`.

Use `push_neg at hq`. Use `set q := B v v with hqe`. Use `set η := -q / (2 * (‖v‖ ^ 2 + 1)) with hη`. Establish `hηpos : 0 < η` using `div_pos (by linarith) (by positivity)`. Establish `ho` using `hasFDerivAt_iff_isLittleO_nhds_zero.mp hψd.hasFDerivAt`.

Establish `e1 : ∀ᶠ h in 𝓝 (0 : Fin n → ℂ), ‖ψ (0 + h) - ψ 0 - B h‖ ≤ η * ‖h‖` using `ho.bound hηpos`. Establish `e2 : ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), DifferentiableAt ℝ f y` using `(hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)`. Establish `e3 : ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), f 0 ≤ f y` using `hm`. Take `⟨δ, hδ, hδh⟩` from `Metric.eventually_nhds_iff.mp (e1.and (e2.and e3))`. Use `set s := δ / (2 * (‖v‖ + 1)) with hs`.

Establish `hspos : 0 < s` using `by positivity`. Establish `hsv : ∀ ξ ∈ Set.Icc 0 s, dist (ξ • v) 0 < δ`. Introduce `ξ hξ`. Rewrite using `[dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hξ.1]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hs, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]`. Use polynomial arithmetic with `[norm_nonneg v]`. Establish `hderiv : ∀ ξ ∈ Set.Icc 0 s, HasDerivAt (fun ξ : ℝ => f (ξ • v)) (ψ (ξ • v) v) ξ`. Introduce `ξ hξ`. Establish `hd` using `(hδh (hsv ξ hξ)).2.1`.

Use `hd.hasFDerivAt.comp_hasDerivAt ξ ((hasDerivAt_id ξ).smul_const v)` as an intermediate fact. Simplify using `only [one_smul, id] at this`. Conclude with `this`. Take `⟨c, hc, hcs⟩` from `exists_hasDerivAt_eq_slope (fun ξ : ℝ => f (ξ • v)) (fun ξ => ψ (ξ • v) v) hspos (fun ξ hξ => (hderiv ξ hξ).continuousAt.continuousWithinAt) (fun ξ hξ => hderiv ξ (Set.Ioo_subset_Icc_self hξ))`. Establish `hcI : c ∈ Set.Icc 0 s` using `Set.Ioo_subset_Icc_self hc`.

Establish `hb` using `(hδh (hsv c hcI)).1`. Simplify using `only [zero_add, hψ0, sub_zero] at hb`. Establish `hfs` using `(hδh (hsv s ⟨hspos.le, le_rfl⟩)).2.2`. Establish `hBc : B (c • v) v = c * q` using `by simp [map_smul, hqe]`. Establish `hbound : ψ (c • v) v ≤ c * q / 2`.

Establish `h1 : |(ψ (c • v) - B (c • v)) v| ≤ η * ‖c • v‖ * ‖v‖`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ‖c • v‖ = c * ‖v‖` using `by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]`. Establish `h3 : (ψ (c • v) - B (c • v)) v = ψ (c • v) v - c * q`. Rewrite using `[ContinuousLinearMap.sub_apply, hBc]`.

Rewrite `h1` using `[h3, h2]`. Establish `h4 : η * (c * ‖v‖) * ‖v‖ ≤ c * (-q / 2)`. Establish `: η * ‖v‖ ^ 2 ≤ -q / 2`. Rewrite using `[hη, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]`. Use polynomial arithmetic with `[sq_nonneg ‖v‖]`.

Use polynomial arithmetic with `[hc.1]`. Use `(abs_le.mp h1).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hneg : ψ (c • v) v < 0` using `by nlinarith [hc.1]`. Rewrite `hneg` using `[hcs]`.

Simplify using `only [zero_smul, sub_zero] at hneg`. Rewrite `hneg` using `[div_lt_iff₀ hspos, zero_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem snd_nonneg (hf : ContDiffAt ℝ 2 f 0) (hm : IsLocalMin f 0) (v : Fin n → ℂ) :
    0 ≤ fderiv ℝ (fderiv ℝ f) 0 v v := by
  set ψ := fderiv ℝ f with hψe
  set B := fderiv ℝ ψ 0 with hB
  have hψd : DifferentiableAt ℝ ψ 0 := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hψ0 : ψ 0 = 0 := hm.fderiv_eq_zero
  by_contra hq
  push_neg at hq
  set q := B v v with hqe
  set η := -q / (2 * (‖v‖ ^ 2 + 1)) with hη
  have hηpos : 0 < η := div_pos (by linarith) (by positivity)
  have ho := hasFDerivAt_iff_isLittleO_nhds_zero.mp hψd.hasFDerivAt
  have e1 : ∀ᶠ h in 𝓝 (0 : Fin n → ℂ), ‖ψ (0 + h) - ψ 0 - B h‖ ≤ η * ‖h‖ := ho.bound hηpos
  have e2 : ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have e3 : ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), f 0 ≤ f y := hm
  obtain ⟨δ, hδ, hδh⟩ := Metric.eventually_nhds_iff.mp (e1.and (e2.and e3))
  set s := δ / (2 * (‖v‖ + 1)) with hs
  have hspos : 0 < s := by positivity
  have hsv : ∀ ξ ∈ Set.Icc 0 s, dist (ξ • v) 0 < δ := by
    intro ξ hξ
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hξ.1]
    calc ξ * ‖v‖ ≤ s * ‖v‖ := mul_le_mul_of_nonneg_right hξ.2 (norm_nonneg _)
      _ < δ := by
        rw [hs, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg v]
  have hderiv : ∀ ξ ∈ Set.Icc 0 s, HasDerivAt (fun ξ : ℝ => f (ξ • v)) (ψ (ξ • v) v) ξ := by
    intro ξ hξ
    have hd := (hδh (hsv ξ hξ)).2.1
    have := hd.hasFDerivAt.comp_hasDerivAt ξ ((hasDerivAt_id ξ).smul_const v)
    simp only [one_smul, id] at this
    exact this
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope (fun ξ : ℝ => f (ξ • v)) (fun ξ => ψ (ξ • v) v) hspos
    (fun ξ hξ => (hderiv ξ hξ).continuousAt.continuousWithinAt)
    (fun ξ hξ => hderiv ξ (Set.Ioo_subset_Icc_self hξ))
  have hcI : c ∈ Set.Icc 0 s := Set.Ioo_subset_Icc_self hc
  have hb := (hδh (hsv c hcI)).1
  simp only [zero_add, hψ0, sub_zero] at hb
  have hfs := (hδh (hsv s ⟨hspos.le, le_rfl⟩)).2.2
  have hBc : B (c • v) v = c * q := by simp [map_smul, hqe]
  have hbound : ψ (c • v) v ≤ c * q / 2 := by
    have h1 : |(ψ (c • v) - B (c • v)) v| ≤ η * ‖c • v‖ * ‖v‖ := by
      calc |(ψ (c • v) - B (c • v)) v| = ‖(ψ (c • v) - B (c • v)) v‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖ψ (c • v) - B (c • v)‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ η * ‖c • v‖ * ‖v‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    have h2 : ‖c • v‖ = c * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    have h3 : (ψ (c • v) - B (c • v)) v = ψ (c • v) v - c * q := by
      rw [ContinuousLinearMap.sub_apply, hBc]
    rw [h3, h2] at h1
    have h4 : η * (c * ‖v‖) * ‖v‖ ≤ c * (-q / 2) := by
      have : η * ‖v‖ ^ 2 ≤ -q / 2 := by
        rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg ‖v‖]
      nlinarith [hc.1]
    have := (abs_le.mp h1).2
    linarith
  have hneg : ψ (c • v) v < 0 := by nlinarith [hc.1]
  rw [hcs] at hneg
  simp only [zero_smul, sub_zero] at hneg
  rw [div_lt_iff₀ hspos, zero_mul] at hneg
  linarith

/- English proof (translation)
Establish `hfg : ContDiffAt ℝ 2 (fun t => f t - g t) 0` using `hf.sub hg.1`. Establish `hmin : IsLocalMin (fun t => f t - g t) 0` using `by filter_upwards [h] with t ht show f 0 - g 0 ≤ f t - g t`. Rewrite using `[h0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum : (fun t => (f t - g t) + g t) = f`.

Use function extensionality and compare the values at `t`. Expand and normalize the polynomial expressions, which then agree. Use `⟨hf, fun w => ?_⟩` and prove the remaining obligations. Establish `e` using `padd_lemma hfg hg.1`. Use `beta_reduce at e`.

Rewrite `e` using `[hsum]`. Establish `e2 : levi f 0 w = (fderiv ℝ (fderiv ℝ (fun t => f t - g t)) 0 w w + fderiv ℝ (fderiv ℝ (fun t => f t - g t)) 0 (Complex.I • w) (Complex.I • w)) / 4 + levi g 0 w`. Unfold `levi`. Rewrite using `[e]`. Simplify using `only [ContinuousLinearMap.add_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Establish `a1` using `snd_nonneg hfg hmin w`. Establish `a2` using `snd_nonneg hfg hmin (Complex.I • w)`. Establish `a3` using `hg.2 w`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ptouch (hf : ContDiffAt ℝ 2 f 0) (hg : PshAt0 g) (h0 : g 0 = f 0) (h : ∀ᶠ t in 𝓝 0, g t ≤ f t) :
    PshAt0 f := by
  have hfg : ContDiffAt ℝ 2 (fun t => f t - g t) 0 := hf.sub hg.1
  have hmin : IsLocalMin (fun t => f t - g t) 0 := by
    filter_upwards [h] with t ht
    show f 0 - g 0 ≤ f t - g t
    rw [h0]
    linarith
  have hsum : (fun t => (f t - g t) + g t) = f := by
    funext t
    ring
  refine ⟨hf, fun w => ?_⟩
  have e := padd_lemma hfg hg.1
  beta_reduce at e
  rw [hsum] at e
  have e2 : levi f 0 w = (fderiv ℝ (fderiv ℝ (fun t => f t - g t)) 0 w w
      + fderiv ℝ (fderiv ℝ (fun t => f t - g t)) 0 (Complex.I • w) (Complex.I • w)) / 4 + levi g 0 w := by
    unfold levi
    rw [e]
    simp only [ContinuousLinearMap.add_apply]
    ring
  rw [e2]
  have a1 := snd_nonneg hfg hmin w
  have a2 := snd_nonneg hfg hmin (Complex.I • w)
  have a3 := hg.2 w
  linarith

end AnalyticReference.An.H
