import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsFactorOrder
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.LogDerivZeros

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.FactorOrderExistence.exists_factor_order`. Consider the case `exact _root_.GlobalTheory.FactorOrderExistence.exists_factor_order`. Consider the case `(apply _root_.GlobalTheory.FactorOrderExistence.exists_factor_order <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.FactorOrderExistence.exists_factor_order <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.FactorOrderExistence.exists_factor_order <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.FactorOrderExistence.exists_factor_order ..)`.
-/
theorem exists_factor_one {U : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) {w : ℂ} (hw : w ∈ U)
    (ho : analyticOrderAt g w ≠ ⊤) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧ (∀ z, g z = (z - w) ^ (analyticOrderNatAt g w) * h z) ∧
      h w ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.FactorOrderExistence.exists_factor_order
  | exact _root_.GlobalTheory.FactorOrderExistence.exists_factor_order
  | (apply _root_.GlobalTheory.FactorOrderExistence.exists_factor_order <;> assumption)
  | (intros; apply _root_.GlobalTheory.FactorOrderExistence.exists_factor_order <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FactorOrderExistence.exists_factor_order <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FactorOrderExistence.exists_factor_order ..)

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨f, hf, by simp, by simp⟩`. Consider the case `insert a S ha ih`. Take `⟨g, hg, hfg, hg0⟩` from `ih (fun w hw => hS w (Finset.mem_insert_of_mem hw)) (fun w hw => ho w (Finset.mem_insert_of_mem hw))`. Establish `haU : a ∈ U` using `hS a (Finset.mem_insert_self _ _)`.

Establish `hP : AnalyticAt ℂ (fun z : ℂ => ∏ w ∈ S, (z - w) ^ (analyticOrderNatAt f w)) a` using `by fun_prop`. Establish `hP0 : (∏ w ∈ S, (a - w) ^ (analyticOrderNatAt f w)) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun w hw => pow_ne_zero _ (sub_ne_zero.2 (by rintro rfl; exact ha hw))`. Establish `hord : analyticOrderAt f a = analyticOrderAt g a`. Establish `e : f = (fun z : ℂ => ∏ w ∈ S, (z - w) ^ (analyticOrderNatAt f w)) * g` using `funext hfg`. Use `analyticOrderAt_mul hP (hg a haU)` as an intermediate fact.

Rewrite `this` using `[← e, hP.analyticOrderAt_eq_zero.2 hP0, zero_add]`. Conclude with `this`. Establish `hordn : analyticOrderNatAt g a = analyticOrderNatAt f a`. Simplify using `[analyticOrderNatAt, hord]`. Take `⟨h, hh, hgh, hh0⟩` from `exists_factor_one hg haU (hord ▸ ho a (Finset.mem_insert_self _ _))`.

Use `⟨h, hh, fun z => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.prod_insert ha, hfg z, hgh z, hordn]`. Expand and normalize the polynomial expressions, which then agree. Break down `Finset.mem_insert.1 hw with rfl | hw` into its components or cases. Conclude with `hh0`.

Introduce `h0`. Conclude with `hg0 w hw (by rw [hgh w, h0, mul_zero])`.
-/
theorem exists_factor {U : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (S : Finset ℂ)
    (hS : ∀ w ∈ S, w ∈ U) (ho : ∀ w ∈ S, analyticOrderAt f w ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      (∀ z, f z = (∏ w ∈ S, (z - w) ^ (analyticOrderNatAt f w)) * g z) ∧ ∀ w ∈ S, g w ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨f, hf, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨g, hg, hfg, hg0⟩ := ih (fun w hw => hS w (Finset.mem_insert_of_mem hw))
      (fun w hw => ho w (Finset.mem_insert_of_mem hw))
    have haU : a ∈ U := hS a (Finset.mem_insert_self _ _)
    have hP : AnalyticAt ℂ (fun z : ℂ => ∏ w ∈ S, (z - w) ^ (analyticOrderNatAt f w)) a := by
      fun_prop
    have hP0 : (∏ w ∈ S, (a - w) ^ (analyticOrderNatAt f w)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun w hw => pow_ne_zero _ (sub_ne_zero.2 (by rintro rfl; exact ha hw))
    have hord : analyticOrderAt f a = analyticOrderAt g a := by
      have e : f = (fun z : ℂ => ∏ w ∈ S, (z - w) ^ (analyticOrderNatAt f w)) * g := funext hfg
      have := analyticOrderAt_mul hP (hg a haU)
      rw [← e, hP.analyticOrderAt_eq_zero.2 hP0, zero_add] at this
      exact this
    have hordn : analyticOrderNatAt g a = analyticOrderNatAt f a := by
      simp [analyticOrderNatAt, hord]
    obtain ⟨h, hh, hgh, hh0⟩ := exists_factor_one hg haU (hord ▸ ho a (Finset.mem_insert_self _ _))
    refine ⟨h, hh, fun z => ?_, fun w hw => ?_⟩
    · rw [Finset.prod_insert ha, hfg z, hgh z, hordn]; ring
    · rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hh0
      · intro h0
        exact hg0 w hw (by rw [hgh w, h0, mul_zero])

/- English proof (translation)
Establish `hR : 0 < R` using `hr.trans hrR`. Establish `hd : DifferentiableOn ℂ (fun u => deriv g u / g u) (Metric.ball 0 R)` using `(hg.deriv Metric.isOpen_ball).div hg h0`. Take `⟨h, hh0, hh⟩` from `hd.isExactOn_ball.with_val_at 0 0`. Establish `hhd : DifferentiableOn ℂ h (Metric.ball 0 R)` using `fun u hu => (hh u hu).differentiableAt.differentiableWithinAt`. Establish `hc : ∀ u ∈ Metric.ball (0 : ℂ) R, g u * cexp (-h u) = g 0`.

Introduce `u hu`. Establish `hD : ∀ v ∈ Metric.ball (0 : ℂ) R, HasDerivAt (fun v => g v * cexp (-h v)) 0 v`. Introduce `v hv`. Establish `h1` using `(hg.differentiableAt (Metric.isOpen_ball.mem_nhds hv)).hasDerivAt`. Establish `h2` using `h1.mul (hh v hv).neg.cexp`.

Use `h0 v hv` as an intermediate fact. Use `HasDerivAt.congr_deriv h2 ?_` and prove the remaining obligations. Simplify using `only [Pi.neg_apply]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `Metric.isOpen_ball.is_const_of_deriv_eq_zero (𝕜 := ℂ) (f := fun v => g v * cexp (-h v)) (convex_ball (0 : ℂ) R).isPreconnected (fun v hv => (hD v hv).differentiableAt.differentiableWithinAt) (fun v hv => (hD v hv).deriv) hu (Metric.mem_ball_self hR)` as an intermediate fact. Simplify `this` using `[hh0]`. Establish `hre : Set.MapsTo h (Metric.ball 0 R) {z | z.re ≤ K}`. Introduce `u hu`. Establish `e : g u = g 0 * cexp (h u)`.

Rewrite using `[← hc u hu, mul_assoc, ← Complex.exp_add]`. Simplify using the standard rewrite rules. Establish `h1` using `hb u hu`. Rewrite `h1` using `[e, norm_mul, Complex.norm_exp]`. Establish `hp : 0 < ‖g 0‖` using `norm_pos_iff.2 (h0 0 (Metric.mem_ball_self hR))`.

Conclude with `Real.exp_le_exp.1 (le_of_mul_le_mul_left h1 hp)`. Establish `hδ : 0 < (R - r) / 2` using `by linarith`. Establish `hsub : Metric.closedBall z ((R - r) / 2) ⊆ Metric.ball 0 R`. Introduce `u hu`. Rewrite `hu` using `[mem_closedBall_iff_norm]`.

Rewrite using `[mem_ball_zero_iff]`. Use `norm_le_norm_sub_add u z` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hzb : z ∈ Metric.ball (0 : ℂ) R` using `hsub (Metric.mem_closedBall_self hδ.le)`. Establish `hcau` using `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (f := h) (C := 2 * K * R / ((R - r) / 2)) hδ (hhd.diffContOnCl_ball hsub) (by`.

Introduce `u hu`. Establish `hu'` using `hsub (Metric.sphere_subset_closedBall hu)`. Establish `h1` using `Complex.borelCaratheodory_zero hK hhd hre hR hu' hh0`. Rewrite `hu` using `[mem_sphere_iff_norm]`. Establish `h2` using `norm_le_norm_sub_add u z`.

Use `h1.trans ?_` and prove the remaining obligations. Use `gcongr`. Conclude with `(mem_ball_zero_iff.1 hu').le`. Use the proof step `linarith)`. Rewrite `hcau` using `[(hh z hzb).deriv]`.

Use `hcau.trans (le_of_eq ?_)` and prove the remaining obligations. Establish `: R - r ≠ 0` using `by linarith`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_logDeriv_le {r R K : ℝ} (hr : 0 < r) (hrR : r < R) (hK : 0 < K) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball 0 R)) (h0 : ∀ z ∈ Metric.ball (0 : ℂ) R, g z ≠ 0)
    (hb : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖g z‖ ≤ ‖g 0‖ * Real.exp K) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖deriv g z / g z‖ ≤ (8 * R / (R - r) ^ 2) * K := by
  have hR : 0 < R := hr.trans hrR
  have hd : DifferentiableOn ℂ (fun u => deriv g u / g u) (Metric.ball 0 R) :=
    (hg.deriv Metric.isOpen_ball).div hg h0
  obtain ⟨h, hh0, hh⟩ := hd.isExactOn_ball.with_val_at 0 0
  have hhd : DifferentiableOn ℂ h (Metric.ball 0 R) :=
    fun u hu => (hh u hu).differentiableAt.differentiableWithinAt
  have hc : ∀ u ∈ Metric.ball (0 : ℂ) R, g u * cexp (-h u) = g 0 := by
    intro u hu
    have hD : ∀ v ∈ Metric.ball (0 : ℂ) R, HasDerivAt (fun v => g v * cexp (-h v)) 0 v := by
      intro v hv
      have h1 := (hg.differentiableAt (Metric.isOpen_ball.mem_nhds hv)).hasDerivAt
      have h2 := h1.mul (hh v hv).neg.cexp
      have := h0 v hv
      refine HasDerivAt.congr_deriv h2 ?_
      simp only [Pi.neg_apply]
      field_simp
      ring
    have := Metric.isOpen_ball.is_const_of_deriv_eq_zero (𝕜 := ℂ) (f := fun v => g v * cexp (-h v))
      (convex_ball (0 : ℂ) R).isPreconnected
      (fun v hv => (hD v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hD v hv).deriv) hu (Metric.mem_ball_self hR)
    simpa [hh0] using this
  have hre : Set.MapsTo h (Metric.ball 0 R) {z | z.re ≤ K} := by
    intro u hu
    have e : g u = g 0 * cexp (h u) := by
      rw [← hc u hu, mul_assoc, ← Complex.exp_add]; simp
    have h1 := hb u hu
    rw [e, norm_mul, Complex.norm_exp] at h1
    have hp : 0 < ‖g 0‖ := norm_pos_iff.2 (h0 0 (Metric.mem_ball_self hR))
    exact Real.exp_le_exp.1 (le_of_mul_le_mul_left h1 hp)
  have hδ : 0 < (R - r) / 2 := by linarith
  have hsub : Metric.closedBall z ((R - r) / 2) ⊆ Metric.ball 0 R := by
    intro u hu
    rw [mem_closedBall_iff_norm] at hu
    rw [mem_ball_zero_iff]
    have := norm_le_norm_sub_add u z
    linarith
  have hzb : z ∈ Metric.ball (0 : ℂ) R := hsub (Metric.mem_closedBall_self hδ.le)
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (f := h)
    (C := 2 * K * R / ((R - r) / 2)) hδ (hhd.diffContOnCl_ball hsub) (by
      intro u hu
      have hu' := hsub (Metric.sphere_subset_closedBall hu)
      have h1 := Complex.borelCaratheodory_zero hK hhd hre hR hu' hh0
      rw [mem_sphere_iff_norm] at hu
      have h2 := norm_le_norm_sub_add u z
      refine h1.trans ?_
      gcongr
      · exact (mem_ball_zero_iff.1 hu').le
      · linarith)
  rw [(hh z hzb).deriv] at hcau
  refine hcau.trans (le_of_eq ?_)
  have : R - r ≠ 0 := by linarith
  field_simp
  ring

/- English proof (translation)
Use `Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball 0 1) Metric.isBounded_ball (hg.differentiableOn.diffContOnCl_ball subset_rfl) ?_ ?_` and prove the remaining obligations. Introduce `u hu`. Rewrite `hu` using `[frontier_ball _ one_ne_zero]`. Conclude with `hb u (by simpa using hu)`. Rewrite using `[closure_ball _ one_ne_zero]`.

Simplify using `using hz`.
-/
theorem norm_le_of_sphere {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (Metric.closedBall 0 1)) {B : ℝ}
    (hb : ∀ z : ℂ, ‖z‖ = 1 → ‖g z‖ ≤ B) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖g z‖ ≤ B := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball 0 1)
    Metric.isBounded_ball (hg.differentiableOn.diffContOnCl_ball subset_rfl) ?_ ?_
  · intro u hu
    rw [frontier_ball _ one_ne_zero] at hu
    exact hb u (by simpa using hu)
  · rw [closure_ball _ one_ne_zero]; simpa using hz

/- English proof (translation)
Establish `h1 : (starRingEnd ℂ) z * z = 1`. Rewrite using `[mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]`. Simplify using the standard rewrite rules. Establish `: 1 - (starRingEnd ℂ) w * z = (starRingEnd ℂ) (z - w) * z`. Rewrite using `[map_sub, sub_mul, h1]`.

Rewrite using `[this, norm_mul, hz, mul_one, Complex.norm_conj]`.
-/
theorem norm_one_sub_conj_mul {w z : ℂ} (hz : ‖z‖ = 1) :
    ‖1 - (starRingEnd ℂ) w * z‖ = ‖z - w‖ := by
  have h1 : (starRingEnd ℂ) z * z = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  have : 1 - (starRingEnd ℂ) w * z = (starRingEnd ℂ) (z - w) * z := by
    rw [map_sub, sub_mul, h1]
  rw [this, norm_mul, hz, mul_one, Complex.norm_conj]

/- English proof (translation)
Introduce `r R hr hrR hR1`. Establish `hR : 0 < R` using `hr.trans hrR`. Establish `hc1 : 0 < -Real.log R` using `neg_pos.2 (Real.log_neg hR hR1)`. Establish `hc2 : 0 < -Real.log (1 - R)` using `neg_pos.2 (Real.log_neg (by linarith) (by linarith))`. Use `set c1 := -Real.log R with hc1d`.

Use `set c2 := -Real.log (1 - R) with hc2d`. Establish `hRr : 0 < R - r` using `by linarith`. Establish `hA : 0 < 8 * R / (R - r) ^ 2` using `by positivity`. Use `set A := 8 * R / (R - r) ^ 2 with hAd`. Use `⟨c1⁻¹ + A * (1 + c1⁻¹ * c2), by positivity, ?_⟩` and prove the remaining obligations.

Introduce `f M hf hf0 hM`. Establish `h0m : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1` using `by simp`. Establish `hf0' : 0 < ‖f 0‖` using `norm_pos_iff.2 hf0`. Establish `hM0 : ‖f 0‖ ≤ M` using `hM 0 h0m`. Establish `hMp : 0 < M` using `hf0'.trans_le hM0`.

Establish `hL : 0 ≤ Real.log (M / ‖f 0‖)` using `Real.log_nonneg ((one_le_div hf0').2 hM0)`. Use `set L := Real.log (M / ‖f 0‖) with hLd`. Establish `hconn` using `(convex_closedBall (0 : ℂ) 1).isPreconnected`. Establish `hfin : {w : ℂ | ‖w‖ ≤ R ∧ f w = 0}.Finite`. Establish `h1` using `hf.preimage_zero_mem_codiscreteWithin hf0 h0m ⟨⟨0, h0m⟩, hconn⟩`.

Use `((isCompact_closedBall (0 : ℂ) 1).finite_sdiff_of_mem_codiscreteWithin h1).subset ?_` and prove the remaining obligations. Introduce and unpack `w ⟨hw, hw0⟩`. Conclude with `⟨by simpa using hw.trans hR1.le, by simpa using hw0⟩`. Use `set S := hfin.toFinset with hSd`. Establish `hS : ∀ w, w ∈ S ↔ ‖w‖ ≤ R ∧ f w = 0` using `fun w => by simp [hSd]`.

Establish `hSU : ∀ w ∈ S, w ∈ Metric.closedBall (0 : ℂ) 1` using `fun w hw => by`. Simplify using `using ((hS w).1 hw).1.trans hR1.le`. Establish `ho : ∀ w ∈ S, analyticOrderAt f w ≠ ⊤` using `fun w hw => hf.analyticOrderAt_ne_top_of_isPreconnected hconn h0m (hSU w hw) (by rw [(hf 0 h0m).analyticOrderAt_eq_zero.2 hf0]; simp)`. Take `⟨g, hg, hfg, hg0⟩` from `exists_factor hf S hSU ho`. Use `set m : ℂ → ℕ := analyticOrderNatAt f with hm`.

Use `set N : ℕ := ∑ w ∈ S, m w with hN`. Establish `hnorm : ∀ z, ‖f z‖ = (∏ w ∈ S, ‖z - w‖ ^ m w) * ‖g z‖` using `fun z => by`. Rewrite using `[hfg z, norm_mul, norm_prod]`. Simplify using `only [norm_pow]`. Establish `hg00 : ‖f 0‖ ≤ R ^ N * ‖g 0‖`.

Rewrite using `[hnorm 0, hN, ← Finset.prod_pow_eq_pow_sum]`. Use `gcongr with w hw`. Simplify using `using ((hS w).1 hw).1`. Establish `hgM : ‖g 0‖ ≤ M`. Establish `hh : AnalyticOnNhd ℂ (fun z => (∏ w ∈ S, (1 - (starRingEnd ℂ) w * z) ^ m w) * g z) (Metric.closedBall 0 1)` using `fun z hz => AnalyticAt.mul (by fun_prop) (hg z hz)`.

Use `norm_le_of_sphere hh (B := M) (z := 0) (fun z hz => by` as an intermediate fact. Establish `h1` using `hM z (by simpa using hz.le)`. Rewrite `h1` using `[hnorm z]`. Rewrite using `[norm_mul, norm_prod]`. Simplify `h1) (by simp)` using `only [norm_pow, norm_one_sub_conj_mul hz]`.

Simplify using `using this`. Establish `hNL : (N : ℝ) ≤ c1⁻¹ * L`. Establish `h1 : ‖f 0‖ ≤ R ^ N * M` using `hg00.trans (by gcongr)`. Establish `h2` using `Real.log_le_log hf0' h1`. Rewrite `h2` using `[Real.log_mul (by positivity) hMp.ne', Real.log_pow]`.

Rewrite using `[← div_eq_inv_mul, le_div_iff₀ hc1, hLd, Real.log_div hMp.ne' hf0'.ne', hc1d]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hRN : R ^ N ≤ 1` using `pow_le_one₀ hR.le hR1.le`. Establish `hg01 : ‖f 0‖ ≤ ‖g 0‖` using `hg00.trans (mul_le_of_le_one_left (norm_nonneg _) hRN)`. Establish `hgB : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖g z‖ ≤ M / (1 - R) ^ N` using `fun z hz => by`.

Use `norm_le_of_sphere hg (fun u hu => ?_) hz` and prove the remaining obligations. Establish `h1R : 0 < 1 - R` using `by linarith`. Rewrite using `[le_div_iff₀ (by positivity), mul_comm]`. Use `le_trans ?_ (hM u (by simpa using hu.le))` and prove the remaining obligations. Rewrite using `[hnorm u, hN, ← Finset.prod_pow_eq_pow_sum]`.

Use `gcongr with w hw`. Use `((hS w).1 hw).1` as an intermediate fact. Use `norm_sub_norm_le u w` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsub : Metric.ball (0 : ℂ) R ⊆ Metric.closedBall 0 1` using `Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hR1.le)`.

Establish `hgne : ∀ z ∈ Metric.ball (0 : ℂ) R, g z ≠ 0` using `fun z hz h0 => hg0 z ((hS z).2 ⟨(mem_ball_zero_iff.1 hz).le, by rw [hfg z, h0, mul_zero]⟩) h0`. Establish `hK : 0 < 1 + L + N * c2` using `by positivity`. Establish `hgb : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖g z‖ ≤ ‖g 0‖ * Real.exp (1 + L + N * c2)`. Introduce `z hz`. Establish `h1R : 0 < 1 - R` using `by linarith`.

Use `(hgB z (by simpa using hsub hz)).trans ?_` and prove the remaining obligations. Establish `e : M / (1 - R) ^ N = ‖f 0‖ * Real.exp (L + N * c2)`. Rewrite using `[Real.exp_add, hLd, Real.exp_log (by positivity), hc2d, mul_neg, Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity)]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hset : {w : ℂ | ‖w‖ ≤ R ∧ f w = 0} = (S : Set ℂ)` using `by simp [hSd]`. Use `⟨⟨hfin, ?_⟩, fun z hz hfz => ?_⟩` and prove the remaining obligations. Rewrite using `[hset, finsum_mem_coe_finset]`.

Establish `: (∑ w ∈ S, (m w : ℝ)) = N` using `by rw [hN]; push_cast; rfl`. Rewrite using `[this]`. Use `hNL.trans ?_` and prove the remaining obligations. Establish `: 0 ≤ A * (1 + c1⁻¹ * c2)` using `by positivity`. Apply the tactic sequence `gcongr <;> linarith`.

Rewrite using `[hset, finsum_mem_coe_finset]`. Establish `hzb : z ∈ Metric.ball (0 : ℂ) R` using `mem_ball_zero_iff.2 (hz.trans_lt hrR)`. Establish `hzw : ∀ w ∈ S, z - w ≠ 0` using `fun w hw h => hfz (by rw [sub_eq_zero.1 h]; exact ((hS w).1 hw).2)`. Establish `hld : deriv f z / f z = ∑ w ∈ S, (m w : ℂ) / (z - w) + deriv g z / g z`. Establish `e : f = fun z => (∏ w ∈ S, (z - w) ^ m w) * g z` using `funext hfg`.

Rewrite using `[← logDeriv_apply, ← logDeriv_apply]`. Use `conv_lhs => rw [e]`. Rewrite using `[logDeriv_mul (f := fun z => ∏ w ∈ S, (z - w) ^ m w) z (Finset.prod_ne_zero_iff.2 fun w hw => pow_ne_zero _ (hzw w hw)) (hgne z hzb) (by fun_prop) (hg z (hsub hzb)).differentiableAt]`. Use `congr 1`. Rewrite using `[logDeriv_prod (f := fun w z => (z - w) ^ m w) (fun w hw => pow_ne_zero _ (hzw w hw)) (fun w hw => by fun_prop)]`.

Use `Finset.sum_congr rfl fun w hw => ?_` and prove the remaining obligations. Rewrite using `[logDeriv_fun_pow (by fun_prop), logDeriv_apply]`. Simplify using `[div_eq_mul_inv]`. Rewrite using `[hld, add_sub_cancel_left]`. Use `(norm_logDeriv_le hr hrR hK (hg.mono hsub).differentiableOn hgne hgb hz).trans ?_` and prove the remaining obligations.

Establish `h1 : 1 + L + N * c2 ≤ (1 + c1⁻¹ * c2) * (1 + L)`. Establish `: N * c2 ≤ c1⁻¹ * L * c2` using `by gcongr`. Establish `: 0 ≤ c1⁻¹ * c2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : 0 ≤ c1⁻¹ * (1 + L)` using `by positivity`.

Establish `h3` using `mul_le_mul_of_nonneg_left h1 hA.le`. Rewrite using `[← hAd]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem main : ∀ r R : ℝ, 0 < r → r < R → R < 1 → ∃ C : ℝ, 0 < C ∧ ∀ (f : ℂ → ℂ) (M : ℝ), AnalyticOnNhd ℂ f (Metric.closedBall 0 1) → f 0 ≠ 0 → (∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖f z‖ ≤ M) → ({w : ℂ | ‖w‖ ≤ R ∧ f w = 0}.Finite ∧ (∑ᶠ w ∈ {w : ℂ | ‖w‖ ≤ R ∧ f w = 0}, (analyticOrderNatAt f w : ℝ)) ≤ C * (1 + Real.log (M / ‖f 0‖))) ∧ ∀ z : ℂ, ‖z‖ ≤ r → f z ≠ 0 → ‖deriv f z / f z - ∑ᶠ w ∈ {w : ℂ | ‖w‖ ≤ R ∧ f w = 0}, (analyticOrderNatAt f w : ℂ) / (z - w)‖ ≤ C * (1 + Real.log (M / ‖f 0‖)) := by
  intro r R hr hrR hR1
  have hR : 0 < R := hr.trans hrR
  have hc1 : 0 < -Real.log R := neg_pos.2 (Real.log_neg hR hR1)
  have hc2 : 0 < -Real.log (1 - R) := neg_pos.2 (Real.log_neg (by linarith) (by linarith))
  set c1 := -Real.log R with hc1d
  set c2 := -Real.log (1 - R) with hc2d
  have hRr : 0 < R - r := by linarith
  have hA : 0 < 8 * R / (R - r) ^ 2 := by positivity
  set A := 8 * R / (R - r) ^ 2 with hAd
  refine ⟨c1⁻¹ + A * (1 + c1⁻¹ * c2), by positivity, ?_⟩
  intro f M hf hf0 hM
  have h0m : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by simp
  have hf0' : 0 < ‖f 0‖ := norm_pos_iff.2 hf0
  have hM0 : ‖f 0‖ ≤ M := hM 0 h0m
  have hMp : 0 < M := hf0'.trans_le hM0
  have hL : 0 ≤ Real.log (M / ‖f 0‖) := Real.log_nonneg ((one_le_div hf0').2 hM0)
  set L := Real.log (M / ‖f 0‖) with hLd
  have hconn := (convex_closedBall (0 : ℂ) 1).isPreconnected
  have hfin : {w : ℂ | ‖w‖ ≤ R ∧ f w = 0}.Finite := by
    have h1 := hf.preimage_zero_mem_codiscreteWithin hf0 h0m ⟨⟨0, h0m⟩, hconn⟩
    refine ((isCompact_closedBall (0 : ℂ) 1).finite_sdiff_of_mem_codiscreteWithin h1).subset ?_
    rintro w ⟨hw, hw0⟩
    exact ⟨by simpa using hw.trans hR1.le, by simpa using hw0⟩
  set S := hfin.toFinset with hSd
  have hS : ∀ w, w ∈ S ↔ ‖w‖ ≤ R ∧ f w = 0 := fun w => by simp [hSd]
  have hSU : ∀ w ∈ S, w ∈ Metric.closedBall (0 : ℂ) 1 := fun w hw => by
    simpa using ((hS w).1 hw).1.trans hR1.le
  have ho : ∀ w ∈ S, analyticOrderAt f w ≠ ⊤ := fun w hw =>
    hf.analyticOrderAt_ne_top_of_isPreconnected hconn h0m (hSU w hw)
      (by rw [(hf 0 h0m).analyticOrderAt_eq_zero.2 hf0]; simp)
  obtain ⟨g, hg, hfg, hg0⟩ := exists_factor hf S hSU ho
  set m : ℂ → ℕ := analyticOrderNatAt f with hm
  set N : ℕ := ∑ w ∈ S, m w with hN
  have hnorm : ∀ z, ‖f z‖ = (∏ w ∈ S, ‖z - w‖ ^ m w) * ‖g z‖ := fun z => by
    rw [hfg z, norm_mul, norm_prod]; simp only [norm_pow]
  have hg00 : ‖f 0‖ ≤ R ^ N * ‖g 0‖ := by
    rw [hnorm 0, hN, ← Finset.prod_pow_eq_pow_sum]
    gcongr with w hw
    simpa using ((hS w).1 hw).1
  have hgM : ‖g 0‖ ≤ M := by
    have hh : AnalyticOnNhd ℂ (fun z => (∏ w ∈ S, (1 - (starRingEnd ℂ) w * z) ^ m w) * g z)
        (Metric.closedBall 0 1) := fun z hz => AnalyticAt.mul (by fun_prop) (hg z hz)
    have := norm_le_of_sphere hh (B := M) (z := 0) (fun z hz => by
      have h1 := hM z (by simpa using hz.le)
      rw [hnorm z] at h1
      rw [norm_mul, norm_prod]
      simpa only [norm_pow, norm_one_sub_conj_mul hz] using h1) (by simp)
    simpa using this
  have hNL : (N : ℝ) ≤ c1⁻¹ * L := by
    have h1 : ‖f 0‖ ≤ R ^ N * M := hg00.trans (by gcongr)
    have h2 := Real.log_le_log hf0' h1
    rw [Real.log_mul (by positivity) hMp.ne', Real.log_pow] at h2
    rw [← div_eq_inv_mul, le_div_iff₀ hc1, hLd, Real.log_div hMp.ne' hf0'.ne', hc1d]
    linarith
  have hRN : R ^ N ≤ 1 := pow_le_one₀ hR.le hR1.le
  have hg01 : ‖f 0‖ ≤ ‖g 0‖ := hg00.trans (mul_le_of_le_one_left (norm_nonneg _) hRN)
  have hgB : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖g z‖ ≤ M / (1 - R) ^ N := fun z hz => by
    refine norm_le_of_sphere hg (fun u hu => ?_) hz
    have h1R : 0 < 1 - R := by linarith
    rw [le_div_iff₀ (by positivity), mul_comm]
    refine le_trans ?_ (hM u (by simpa using hu.le))
    rw [hnorm u, hN, ← Finset.prod_pow_eq_pow_sum]
    gcongr with w hw
    have := ((hS w).1 hw).1
    have := norm_sub_norm_le u w
    linarith
  have hsub : Metric.ball (0 : ℂ) R ⊆ Metric.closedBall 0 1 :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hR1.le)
  have hgne : ∀ z ∈ Metric.ball (0 : ℂ) R, g z ≠ 0 := fun z hz h0 =>
    hg0 z ((hS z).2 ⟨(mem_ball_zero_iff.1 hz).le, by rw [hfg z, h0, mul_zero]⟩) h0
  have hK : 0 < 1 + L + N * c2 := by positivity
  have hgb : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖g z‖ ≤ ‖g 0‖ * Real.exp (1 + L + N * c2) := by
    intro z hz
    have h1R : 0 < 1 - R := by linarith
    refine (hgB z (by simpa using hsub hz)).trans ?_
    have e : M / (1 - R) ^ N = ‖f 0‖ * Real.exp (L + N * c2) := by
      rw [Real.exp_add, hLd, Real.exp_log (by positivity), hc2d, mul_neg, Real.exp_neg,
        ← Real.log_pow, Real.exp_log (by positivity)]
      field_simp
    rw [e]
    gcongr
    linarith
  have hset : {w : ℂ | ‖w‖ ≤ R ∧ f w = 0} = (S : Set ℂ) := by simp [hSd]
  refine ⟨⟨hfin, ?_⟩, fun z hz hfz => ?_⟩
  · rw [hset, finsum_mem_coe_finset]
    have : (∑ w ∈ S, (m w : ℝ)) = N := by rw [hN]; push_cast; rfl
    rw [this]
    refine hNL.trans ?_
    have : 0 ≤ A * (1 + c1⁻¹ * c2) := by positivity
    gcongr <;> linarith
  · rw [hset, finsum_mem_coe_finset]
    have hzb : z ∈ Metric.ball (0 : ℂ) R := mem_ball_zero_iff.2 (hz.trans_lt hrR)
    have hzw : ∀ w ∈ S, z - w ≠ 0 := fun w hw h => hfz (by rw [sub_eq_zero.1 h]; exact ((hS w).1 hw).2)
    have hld : deriv f z / f z = ∑ w ∈ S, (m w : ℂ) / (z - w) + deriv g z / g z := by
      have e : f = fun z => (∏ w ∈ S, (z - w) ^ m w) * g z := funext hfg
      rw [← logDeriv_apply, ← logDeriv_apply]
      conv_lhs => rw [e]
      rw [logDeriv_mul (f := fun z => ∏ w ∈ S, (z - w) ^ m w) z
        (Finset.prod_ne_zero_iff.2 fun w hw => pow_ne_zero _ (hzw w hw)) (hgne z hzb)
        (by fun_prop) (hg z (hsub hzb)).differentiableAt]
      congr 1
      rw [logDeriv_prod (f := fun w z => (z - w) ^ m w) (fun w hw => pow_ne_zero _ (hzw w hw))
        (fun w hw => by fun_prop)]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [logDeriv_fun_pow (by fun_prop), logDeriv_apply]
      simp [div_eq_mul_inv]
    rw [hld, add_sub_cancel_left]
    refine (norm_logDeriv_le hr hrR hK (hg.mono hsub).differentiableOn hgne hgb hz).trans ?_
    have h1 : 1 + L + N * c2 ≤ (1 + c1⁻¹ * c2) * (1 + L) := by
      have : N * c2 ≤ c1⁻¹ * L * c2 := by gcongr
      have : 0 ≤ c1⁻¹ * c2 := by positivity
      nlinarith
    have h2 : 0 ≤ c1⁻¹ * (1 + L) := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 hA.le
    rw [← hAd]
    nlinarith

end GlobalTheory.LogDerivZeros
