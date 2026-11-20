import Mathlib

open MeasureTheory Set
open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Set `ψ : ContDiffBump (ρ / 2 : ℝ)` to `⟨ρ / 2 - 2 * ε, ρ / 2 - ε, by linarith, by linarith⟩`. Establish `hψc : Continuous ψ` using `ψ.continuous`. Establish `hψ0 : ∀ t, t ≤ ε ∨ ρ - ε ≤ t → ψ t = 0`. Introduce `t ht`. Apply `ψ.zero_of_le_dist` to reduce the goal to its premises.

Rewrite using `[Real.dist_eq]`. Use `show ρ / 2 - ε ≤ |t - ρ / 2|`. Break down `ht with ht | ht` into its components or cases. Rewrite using `[abs_sub_comm]; exact le_trans (by linarith) (le_abs_self _)`. Conclude with `le_trans (by linarith) (le_abs_self _)`.

Establish `hψ1 : ∀ t, 2 * ε ≤ t → t ≤ ρ - 2 * ε → ψ t = 1`. Introduce `t h1 h2`. Apply `ψ.one_of_mem_closedBall` to reduce the goal to its premises. Rewrite using `[Metric.mem_closedBall, Real.dist_eq]`. Use `show |t - ρ / 2| ≤ ρ / 2 - 2 * ε`.

Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`. Establish `hII : ∀ a b, IntervalIntegrable ψ volume a b` using `fun a b => hψc.intervalIntegrable a b`. Take `⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun u => ∫ t in ε..u, ψ t` from `⟨_, rfl⟩`. Establish `hFd : ∀ u, HasDerivAt F (ψ u) u`. Introduce `u`.

Rewrite using `[hF]`. Conclude with `(hψc.integral_hasStrictDerivAt ε u).hasDerivAt`. Establish `hFs : ContDiff ℝ ∞ F`. Use `contDiff_infty_iff_deriv.2 ⟨fun u => (hFd u).differentiableAt, ?_⟩` and prove the remaining obligations. Establish `h : deriv F = ψ` using `funext fun u => (hFd u).deriv`.

Rewrite using `[h]`. Conclude with `ψ.contDiff`. Establish `hFlow : ∀ u, u ≤ ε → F u = 0`. Introduce `u hu`. Rewrite using `[hF]`.

Use `show ∫ t in ε..u, ψ t = 0`. Rewrite using `[intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]`. Simplify using the standard rewrite rules. Introduce `t ht`. Conclude with `hψ0 t (Or.inl (le_trans ht.2 (sup_le le_rfl hu)))`.

Take `⟨I, hI⟩ : ∃ I : ℝ, I = ∫ t in ε..(ρ - ε), ψ t` from `⟨_, rfl⟩`. Establish `hFhigh : ∀ u, ρ - ε ≤ u → F u = I`. Introduce `u hu`. Rewrite using `[hF, hI]`. Use `show ∫ t in ε..u, ψ t = ∫ t in ε..(ρ - ε), ψ t`.

Rewrite using `[← intervalIntegral.integral_add_adjacent_intervals (hII ε (ρ - ε)) (hII (ρ - ε) u), intervalIntegral.integral_congr (a := ρ - ε) (b := u) (g := fun _ => (0 : ℝ)) ?_]`. Simplify using the standard rewrite rules. Introduce `t ht`. Conclude with `hψ0 t (Or.inr (le_trans (le_inf le_rfl hu) ht.1))`. Establish `hIge : ρ - 4 * ε ≤ I`.

Rewrite using `[hI]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[intervalIntegral.integral_const, smul_eq_mul, mul_one]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∫ t in (2 * ε)..(ρ - 2 * ε), ψ t := by`.

Apply `intervalIntegral.integral_congr` to reduce the goal to its premises. Introduce `t ht`. Rewrite `ht` using `[Set.uIcc_of_le (by linarith)]`. Conclude with `(hψ1 t ht.1 ht.2).symm`. Use `_ ≤ ∫ t in ε..(ρ - ε), ψ t := intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith) (Filter.Eventually.of_forall fun t => ψ.nonneg) (hII _ _)`.

Establish `hIpos : 0 < I` using `by linarith`. Establish `hFrange : ∀ u, 0 ≤ F u ∧ F u ≤ I`. Introduce `u`. Break down `le_total u ε with h | h` into its components or cases. Rewrite using `[hFlow u h]`.

Conclude with `⟨le_rfl, hIpos.le⟩`. Break down `le_total (ρ - ε) u with h' | h'` into its components or cases. Rewrite using `[hFhigh u h']`. Conclude with `⟨hIpos.le, le_rfl⟩`. Establish `hsplit : F u + ∫ t in u..(ρ - ε), ψ t = I`.

Rewrite using `[hF, hI]`. Conclude with `intervalIntegral.integral_add_adjacent_intervals (hII _ _) (hII _ _)`. Establish `h1 : 0 ≤ F u`. Rewrite using `[hF]`. Conclude with `intervalIntegral.integral_nonneg h fun t _ => ψ.nonneg`.

Establish `h2 : 0 ≤ ∫ t in u..(ρ - ε), ψ t` using `intervalIntegral.integral_nonneg h' fun t _ => ψ.nonneg`. Conclude with `⟨h1, by linarith⟩`. Use `⟨fun u => 1 - F u / I, contDiff_const.sub (hFs.div_const I), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Simplify using `[hFlow u hu]`.

Introduce `u hu`. Simplify using `[hFhigh u hu, hIpos.ne']`. Introduce `u`. Rewrite using `[sub_nonneg, div_le_one hIpos]`. Conclude with `(hFrange u).2`.

Introduce `u`. Establish `: 0 ≤ F u / I` using `div_nonneg (hFrange u).1 hIpos.le`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `u`. Establish `hd : HasDerivAt (fun u => 1 - F u / I) (-(ψ u / I)) u` using `((hFd u).div_const I).const_sub 1`.

Rewrite using `[hd.deriv, neg_le_neg_iff, div_le_div_iff₀ hIpos (by linarith)]`. Use polynomial arithmetic with `[ψ.le_one (x := u), ψ.nonneg (x := u)]`.
-/
theorem exists_smooth_step_sharp_slope (ρ ε : ℝ) (hε : 0 < ε) (h4 : 4 * ε < ρ) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ (∀ u, u ≤ ε → η u = 1) ∧ (∀ u, ρ - ε ≤ u → η u = 0) ∧
      (∀ u, 0 ≤ η u) ∧ (∀ u, η u ≤ 1) ∧ ∀ u, -(1 / (ρ - 4 * ε)) ≤ deriv η u := by
  let ψ : ContDiffBump (ρ / 2 : ℝ) := ⟨ρ / 2 - 2 * ε, ρ / 2 - ε, by linarith, by linarith⟩
  have hψc : Continuous ψ := ψ.continuous
  have hψ0 : ∀ t, t ≤ ε ∨ ρ - ε ≤ t → ψ t = 0 := by
    intro t ht
    apply ψ.zero_of_le_dist
    rw [Real.dist_eq]
    show ρ / 2 - ε ≤ |t - ρ / 2|
    rcases ht with ht | ht
    · rw [abs_sub_comm]; exact le_trans (by linarith) (le_abs_self _)
    · exact le_trans (by linarith) (le_abs_self _)
  have hψ1 : ∀ t, 2 * ε ≤ t → t ≤ ρ - 2 * ε → ψ t = 1 := by
    intro t h1 h2
    apply ψ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq]
    show |t - ρ / 2| ≤ ρ / 2 - 2 * ε
    rw [abs_le]; constructor <;> linarith
  have hII : ∀ a b, IntervalIntegrable ψ volume a b := fun a b => hψc.intervalIntegrable a b
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun u => ∫ t in ε..u, ψ t := ⟨_, rfl⟩
  have hFd : ∀ u, HasDerivAt F (ψ u) u := by
    intro u; rw [hF]; exact (hψc.integral_hasStrictDerivAt ε u).hasDerivAt
  have hFs : ContDiff ℝ ∞ F := by
    refine contDiff_infty_iff_deriv.2 ⟨fun u => (hFd u).differentiableAt, ?_⟩
    have h : deriv F = ψ := funext fun u => (hFd u).deriv
    rw [h]; exact ψ.contDiff
  have hFlow : ∀ u, u ≤ ε → F u = 0 := by
    intro u hu
    rw [hF]
    show ∫ t in ε..u, ψ t = 0
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      exact hψ0 t (Or.inl (le_trans ht.2 (sup_le le_rfl hu)))
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ t in ε..(ρ - ε), ψ t := ⟨_, rfl⟩
  have hFhigh : ∀ u, ρ - ε ≤ u → F u = I := by
    intro u hu
    rw [hF, hI]
    show ∫ t in ε..u, ψ t = ∫ t in ε..(ρ - ε), ψ t
    rw [← intervalIntegral.integral_add_adjacent_intervals (hII ε (ρ - ε)) (hII (ρ - ε) u),
      intervalIntegral.integral_congr (a := ρ - ε) (b := u) (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      exact hψ0 t (Or.inr (le_trans (le_inf le_rfl hu) ht.1))
  have hIge : ρ - 4 * ε ≤ I := by
    rw [hI]
    calc ρ - 4 * ε = ∫ _ in (2 * ε)..(ρ - 2 * ε), (1 : ℝ) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]; ring
      _ = ∫ t in (2 * ε)..(ρ - 2 * ε), ψ t := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le (by linarith)] at ht
          exact (hψ1 t ht.1 ht.2).symm
      _ ≤ ∫ t in ε..(ρ - ε), ψ t :=
          intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
            (Filter.Eventually.of_forall fun t => ψ.nonneg) (hII _ _)
  have hIpos : 0 < I := by linarith
  have hFrange : ∀ u, 0 ≤ F u ∧ F u ≤ I := by
    intro u
    rcases le_total u ε with h | h
    · rw [hFlow u h]; exact ⟨le_rfl, hIpos.le⟩
    rcases le_total (ρ - ε) u with h' | h'
    · rw [hFhigh u h']; exact ⟨hIpos.le, le_rfl⟩
    have hsplit : F u + ∫ t in u..(ρ - ε), ψ t = I := by
      rw [hF, hI]; exact intervalIntegral.integral_add_adjacent_intervals (hII _ _) (hII _ _)
    have h1 : 0 ≤ F u := by
      rw [hF]; exact intervalIntegral.integral_nonneg h fun t _ => ψ.nonneg
    have h2 : 0 ≤ ∫ t in u..(ρ - ε), ψ t := intervalIntegral.integral_nonneg h' fun t _ => ψ.nonneg
    exact ⟨h1, by linarith⟩
  refine ⟨fun u => 1 - F u / I, contDiff_const.sub (hFs.div_const I), ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu; simp [hFlow u hu]
  · intro u hu; simp [hFhigh u hu, hIpos.ne']
  · intro u
    rw [sub_nonneg, div_le_one hIpos]; exact (hFrange u).2
  · intro u
    have : 0 ≤ F u / I := div_nonneg (hFrange u).1 hIpos.le
    linarith
  · intro u
    have hd : HasDerivAt (fun u => 1 - F u / I) (-(ψ u / I)) u :=
      ((hFd u).div_const I).const_sub 1
    rw [hd.deriv, neg_le_neg_iff, div_le_div_iff₀ hIpos (by linarith)]
    nlinarith [ψ.le_one (x := u), ψ.nonneg (x := u)]

/- English proof (translation)
Introduce `ρ0 θ hρ hθ`. Take `⟨ε, hε, hE⟩ : ∃ ε : ℝ, 0 < ε ∧ 8 * θ * ε = ρ0 * (θ - 1)` from `⟨ρ0 * (θ - 1) / (8 * θ), div_pos (mul_pos hρ (by linarith)) (by linarith), by field_simp⟩`. Establish `h4 : 4 * ε < ρ0` using `by nlinarith`. Establish `hpos : 0 < ρ0 - 4 * ε` using `by linarith`. Establish `hslope : 1 / (ρ0 - 4 * ε) ≤ θ / ρ0`.

Rewrite using `[one_div_le hpos (by positivity), one_div_div, div_le_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨η, hηs, hη1, hη0, hηnn, hηle, hηd⟩` from `exists_smooth_step_sharp_slope ρ0 ε hε h4`. Use `⟨ε, 2 * ρ0 / ε + |Real.log ε|, hε, by linarith, ?_⟩` and prove the remaining obligations. Introduce `δ hδ _`.

Take `⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun t => η t / (t + δ)` from `⟨_, rfl⟩`. Establish `hfv : ∀ t, f t = η t / (t + δ)` using `fun t => by rw [hf]`. Establish `hfc : ContDiffOn ℝ ∞ f (Set.Ioi (-δ))`. Rewrite using `[hf]`. Use `hηs.contDiffOn.div (contDiffOn_id.add contDiffOn_const) fun t ht => ?_` and prove the remaining obligations.

Establish `h : 0 < t + δ` using `by simp only [Set.mem_Ioi] at ht; linarith`. Conclude with `h.ne'`. Establish `hfcont` using `hfc.continuousOn`. Establish `hsub : ∀ a b, -δ < a → -δ < b → Set.uIcc a b ⊆ Set.Ioi (-δ)` using `fun a b ha hb t ht => lt_of_lt_of_le (lt_inf_iff.2 ⟨ha, hb⟩) ht.1`. Establish `hII : ∀ a b, -δ < a → -δ < b → IntervalIntegrable f volume a b` using `fun a b ha hb => (hfcont.mono (hsub a b ha hb)).intervalIntegrable`.

Establish `hd : ∀ u, -δ < u → HasDerivAt (fun u => ∫ t in ρ0..u, f t) (f u) u` using `fun u hu => intervalIntegral.integral_hasDerivAt_right (hII ρ0 u (by linarith) hu) (hfcont.stronglyMeasurableAtFilter isOpen_Ioi u hu) (hfcont.continuousAt (isOpen_Ioi.mem_nhds hu))`. Establish `hnn : ∀ t, -δ < t → 0 ≤ f t` using `fun t ht => by`. Rewrite using `[hfv]; exact div_nonneg (hηnn t) (by linarith)`. Establish `hzero : ∀ u, ρ0 - ε ≤ u → ∫ t in ρ0..u, f t = 0`. Introduce `u hu`.

Rewrite using `[intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]`. Simplify using the standard rewrite rules. Introduce `t ht`. Establish `h : ρ0 - ε ≤ t` using `le_trans (le_inf (by linarith) hu) ht.1`. Simplify using `only [hfv, hη0 t h, zero_div]`.

Establish `hle0 : ∀ u, 0 ≤ u → ∫ t in ρ0..u, f t ≤ 0`. Introduce `u hu`. Break down `le_total u ρ0 with h | h` into its components or cases. Rewrite using `[intervalIntegral.integral_symm]`. Use `intervalIntegral.integral_nonneg (μ := volume) h fun t ht => hnn t (lt_of_lt_of_le (by linarith) ht.1)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hzero u (by linarith)]`. Use `⟨fun u => ∫ t in ρ0..u, f t, ?_, hzero, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).2 ⟨fun u hu => (hd u hu).differentiableAt.differentiableWithinAt, hfc.congr fun u hu => (hd u hu).deriv⟩`. Introduce `u hu`.

Establish `hu' : -δ < u` using `by linarith`. Establish `hp : 0 < u + δ` using `by linarith`. Establish `hdg : deriv (fun u => ∫ t in ρ0..u, f t) u = f u` using `(hd u hu').deriv`. Establish `hηdiff : HasDerivAt η (deriv η u) u` using `((hηs.differentiable (by simp)) u).hasDerivAt`. Establish `hfd : HasDerivAt f ((deriv η u * (u + δ) - η u * 1) / (u + δ) ^ 2) u`.

Rewrite using `[hf]`. Conclude with `hηdiff.fun_div ((hasDerivAt_id u).add_const δ) hp.ne'`. Establish `hdd : deriv (deriv (fun u => ∫ t in ρ0..u, f t)) u = deriv f u`. Apply `Filter.EventuallyEq.deriv_eq` to reduce the goal to its premises. Use `filter_upwards [isOpen_Ioi.mem_nhds hu'] with t ht using (hd t ht).deriv`.

Use `⟨hle0 u hu, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hdg, hfv]`. Conclude with `div_nonneg (hηnn u) hp.le`. Rewrite using `[hdg, hdd, hfd.deriv, hfv]`. Establish `ha : 0 < 1 / (ρ0 - 4 * ε)` using `by positivity`.

Establish `key : η u / (u + δ) + u * ((deriv η u * (u + δ) - η u * 1) / (u + δ) ^ 2) = η u * δ / (u + δ) ^ 2 + u * deriv η u / (u + δ)` using `by field_simp; ring`. Rewrite using `[key]`. Establish `h1 : 0 ≤ η u * δ / (u + δ) ^ 2` using `div_nonneg (mul_nonneg (hηnn u) hδ.le) (sq_nonneg _)`. Establish `h2 : -(1 / (ρ0 - 4 * ε)) ≤ u * deriv η u / (u + δ)`. Rewrite using `[le_div_iff₀ hp]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left (hηd u) hu, mul_pos ha hδ]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `u hu0 huε beta_reduce`. Establish `hp : 0 < u + δ` using `by linarith`. Establish `hεδ : 0 < ε + δ` using `by linarith`.

Establish `hsplit : ∫ t in ρ0..u, f t = (∫ t in ρ0..ε, f t) - ∫ t in u..ε, f t`. Rewrite using `[← intervalIntegral.integral_add_adjacent_intervals (hII ρ0 ε (by linarith) (by linarith)) (hII ε u (by linarith) (by linarith)), intervalIntegral.integral_symm u ε]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlog : ∫ t in u..ε, f t = Real.log (ε + δ) - Real.log (u + δ)`. Rewrite using `[intervalIntegral.integral_congr (g := fun t => (t + δ)⁻¹) ?_]`.

Establish `h` using `intervalIntegral.integral_comp_add_right (a := u) (b := ε) (fun t : ℝ => t⁻¹) δ`. Rewrite using `[h, integral_inv_of_pos hp hεδ, Real.log_div hεδ.ne' hp.ne']`. Introduce `t ht`. Establish `h : t ≤ ε` using `le_trans ht.2 (sup_le huε le_rfl)`. Simplify using `only [hfv, hη1 t h, one_div]`.

Rewrite using `[hsplit, hlog]`. Establish `h1` using `hle0 ε hε.le`. Establish `h2 : Real.log ε ≤ Real.log (ε + δ)` using `Real.log_le_log hε (by linarith)`. Establish `h3` using `neg_abs_le (Real.log ε)`. Establish `h5 : 0 ≤ 2 * ρ0 / ε` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `u hu beta_reduce`. Establish `hC : 0 ≤ 2 * ρ0 / ε + |Real.log ε|` using `by positivity`. Break down `le_total u ρ0 with h | h` into its components or cases. Establish `hu' : -δ < u` using `by linarith`.

Rewrite using `[intervalIntegral.integral_symm]`. Establish `hb : ∫ t in u..ρ0, f t ≤ ∫ _ in u..ρ0, (2 / ε)`. Use `intervalIntegral.integral_mono_on h (hII u ρ0 hu' (by linarith)) intervalIntegrable_const fun t ht => ?_` and prove the remaining obligations. Establish `ht1 : ε / 2 ≤ t` using `le_trans hu ht.1`. Establish `hk : 2 / ε * ε = 2` using `div_mul_cancel₀ 2 hε.ne'`.

Rewrite using `[hfv, div_le_iff₀ (by linarith)]`. Use polynomial arithmetic with `[hηle t, mul_nonneg (div_pos two_pos hε).le (show 0 ≤ t + δ - ε / 2 by linarith)]`. Rewrite `hb` using `[intervalIntegral.integral_const, smul_eq_mul]`. Establish `hm : (ρ0 - u) * (2 / ε) ≤ 2 * ρ0 / ε`. Rewrite using `[show 2 * ρ0 / ε = ρ0 * (2 / ε) by ring]`.

Conclude with `mul_le_mul_of_nonneg_right (by linarith) (by positivity)`. Use `abs_nonneg (Real.log ε)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hzero u (by linarith)]; linarith`.
-/
theorem exists_cutoff_log_sharp : ∀ ρ0 θ : ℝ, 0 < ρ0 → 1 < θ → ∃ ε C : ℝ, 0 < ε ∧ ε < ρ0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ g : ℝ → ℝ,
    ContDiffOn ℝ ∞ g (Set.Ioi (-δ)) ∧ (∀ u, ρ0 - ε ≤ u → g u = 0) ∧
    (∀ u, 0 ≤ u → g u ≤ 0 ∧ 0 ≤ deriv g u ∧ -(θ / ρ0) ≤ deriv g u + u * deriv (deriv g) u) ∧
    (∀ u, 0 ≤ u → u ≤ ε → g u ≤ Real.log (u + δ) + C) ∧ ∀ u, ε / 2 ≤ u → -C ≤ g u := by
  intro ρ0 θ hρ hθ
  obtain ⟨ε, hε, hE⟩ : ∃ ε : ℝ, 0 < ε ∧ 8 * θ * ε = ρ0 * (θ - 1) :=
    ⟨ρ0 * (θ - 1) / (8 * θ), div_pos (mul_pos hρ (by linarith)) (by linarith), by field_simp⟩
  have h4 : 4 * ε < ρ0 := by nlinarith
  have hpos : 0 < ρ0 - 4 * ε := by linarith
  have hslope : 1 / (ρ0 - 4 * ε) ≤ θ / ρ0 := by
    rw [one_div_le hpos (by positivity), one_div_div, div_le_iff₀ (by linarith)]
    nlinarith
  obtain ⟨η, hηs, hη1, hη0, hηnn, hηle, hηd⟩ := exists_smooth_step_sharp_slope ρ0 ε hε h4
  refine ⟨ε, 2 * ρ0 / ε + |Real.log ε|, hε, by linarith, ?_⟩
  intro δ hδ _
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun t => η t / (t + δ) := ⟨_, rfl⟩
  have hfv : ∀ t, f t = η t / (t + δ) := fun t => by rw [hf]
  have hfc : ContDiffOn ℝ ∞ f (Set.Ioi (-δ)) := by
    rw [hf]
    refine hηs.contDiffOn.div (contDiffOn_id.add contDiffOn_const) fun t ht => ?_
    have h : 0 < t + δ := by simp only [Set.mem_Ioi] at ht; linarith
    exact h.ne'
  have hfcont := hfc.continuousOn
  have hsub : ∀ a b, -δ < a → -δ < b → Set.uIcc a b ⊆ Set.Ioi (-δ) := fun a b ha hb t ht =>
    lt_of_lt_of_le (lt_inf_iff.2 ⟨ha, hb⟩) ht.1
  have hII : ∀ a b, -δ < a → -δ < b → IntervalIntegrable f volume a b :=
    fun a b ha hb => (hfcont.mono (hsub a b ha hb)).intervalIntegrable
  have hd : ∀ u, -δ < u → HasDerivAt (fun u => ∫ t in ρ0..u, f t) (f u) u := fun u hu =>
    intervalIntegral.integral_hasDerivAt_right (hII ρ0 u (by linarith) hu)
      (hfcont.stronglyMeasurableAtFilter isOpen_Ioi u hu)
      (hfcont.continuousAt (isOpen_Ioi.mem_nhds hu))
  have hnn : ∀ t, -δ < t → 0 ≤ f t := fun t ht => by
    rw [hfv]; exact div_nonneg (hηnn t) (by linarith)
  have hzero : ∀ u, ρ0 - ε ≤ u → ∫ t in ρ0..u, f t = 0 := by
    intro u hu
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      have h : ρ0 - ε ≤ t := le_trans (le_inf (by linarith) hu) ht.1
      simp only [hfv, hη0 t h, zero_div]
  have hle0 : ∀ u, 0 ≤ u → ∫ t in ρ0..u, f t ≤ 0 := by
    intro u hu
    rcases le_total u ρ0 with h | h
    · rw [intervalIntegral.integral_symm]
      have := intervalIntegral.integral_nonneg (μ := volume) h fun t ht =>
        hnn t (lt_of_lt_of_le (by linarith) ht.1)
      linarith
    · rw [hzero u (by linarith)]
  refine ⟨fun u => ∫ t in ρ0..u, f t, ?_, hzero, ?_, ?_, ?_⟩
  · exact (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).2
      ⟨fun u hu => (hd u hu).differentiableAt.differentiableWithinAt,
       hfc.congr fun u hu => (hd u hu).deriv⟩
  · intro u hu
    have hu' : -δ < u := by linarith
    have hp : 0 < u + δ := by linarith
    have hdg : deriv (fun u => ∫ t in ρ0..u, f t) u = f u := (hd u hu').deriv
    have hηdiff : HasDerivAt η (deriv η u) u := ((hηs.differentiable (by simp)) u).hasDerivAt
    have hfd : HasDerivAt f ((deriv η u * (u + δ) - η u * 1) / (u + δ) ^ 2) u := by
      rw [hf]; exact hηdiff.fun_div ((hasDerivAt_id u).add_const δ) hp.ne'
    have hdd : deriv (deriv (fun u => ∫ t in ρ0..u, f t)) u = deriv f u := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [isOpen_Ioi.mem_nhds hu'] with t ht using (hd t ht).deriv
    refine ⟨hle0 u hu, ?_, ?_⟩
    · rw [hdg, hfv]; exact div_nonneg (hηnn u) hp.le
    · rw [hdg, hdd, hfd.deriv, hfv]
      have ha : 0 < 1 / (ρ0 - 4 * ε) := by positivity
      have key : η u / (u + δ) + u * ((deriv η u * (u + δ) - η u * 1) / (u + δ) ^ 2)
          = η u * δ / (u + δ) ^ 2 + u * deriv η u / (u + δ) := by
        field_simp; ring
      rw [key]
      have h1 : 0 ≤ η u * δ / (u + δ) ^ 2 := div_nonneg (mul_nonneg (hηnn u) hδ.le) (sq_nonneg _)
      have h2 : -(1 / (ρ0 - 4 * ε)) ≤ u * deriv η u / (u + δ) := by
        rw [le_div_iff₀ hp]
        nlinarith [mul_le_mul_of_nonneg_left (hηd u) hu, mul_pos ha hδ]
      linarith
  · intro u hu0 huε
    beta_reduce
    have hp : 0 < u + δ := by linarith
    have hεδ : 0 < ε + δ := by linarith
    have hsplit : ∫ t in ρ0..u, f t = (∫ t in ρ0..ε, f t) - ∫ t in u..ε, f t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hII ρ0 ε (by linarith) (by linarith)) (hII ε u (by linarith) (by linarith)),
        intervalIntegral.integral_symm u ε]
      ring
    have hlog : ∫ t in u..ε, f t = Real.log (ε + δ) - Real.log (u + δ) := by
      rw [intervalIntegral.integral_congr (g := fun t => (t + δ)⁻¹) ?_]
      · have h := intervalIntegral.integral_comp_add_right (a := u) (b := ε) (fun t : ℝ => t⁻¹) δ
        rw [h, integral_inv_of_pos hp hεδ, Real.log_div hεδ.ne' hp.ne']
      · intro t ht
        have h : t ≤ ε := le_trans ht.2 (sup_le huε le_rfl)
        simp only [hfv, hη1 t h, one_div]
    rw [hsplit, hlog]
    have h1 := hle0 ε hε.le
    have h2 : Real.log ε ≤ Real.log (ε + δ) := Real.log_le_log hε (by linarith)
    have h3 := neg_abs_le (Real.log ε)
    have h5 : 0 ≤ 2 * ρ0 / ε := by positivity
    linarith
  · intro u hu
    beta_reduce
    have hC : 0 ≤ 2 * ρ0 / ε + |Real.log ε| := by positivity
    rcases le_total u ρ0 with h | h
    · have hu' : -δ < u := by linarith
      rw [intervalIntegral.integral_symm]
      have hb : ∫ t in u..ρ0, f t ≤ ∫ _ in u..ρ0, (2 / ε) := by
        refine intervalIntegral.integral_mono_on h (hII u ρ0 hu' (by linarith))
          intervalIntegrable_const fun t ht => ?_
        have ht1 : ε / 2 ≤ t := le_trans hu ht.1
        have hk : 2 / ε * ε = 2 := div_mul_cancel₀ 2 hε.ne'
        rw [hfv, div_le_iff₀ (by linarith)]
        nlinarith [hηle t, mul_nonneg (div_pos two_pos hε).le (show 0 ≤ t + δ - ε / 2 by linarith)]
      rw [intervalIntegral.integral_const, smul_eq_mul] at hb
      have hm : (ρ0 - u) * (2 / ε) ≤ 2 * ρ0 / ε := by
        rw [show 2 * ρ0 / ε = ρ0 * (2 / ε) by ring]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have := abs_nonneg (Real.log ε)
      linarith
    · rw [hzero u (by linarith)]; linarith

end GlobalTheory
