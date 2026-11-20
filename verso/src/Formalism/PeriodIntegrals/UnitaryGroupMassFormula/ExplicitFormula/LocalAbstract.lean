import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LogDerivBoundOfZeroFree
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.NormLogDerivReflLe

noncomputable section

namespace PI.EF.Loc

open Complex Metric Set Filter Topology

def locC (r R' R : ℝ) : ℝ :=
  4 * (r + R') / (R' - r) ^ 2 + R' / (R * (R - R')) / Real.log (R / R')

/- English proof (translation)
Establish `hR' : 0 < R'` using `hr.trans hrR'`. Establish `hR : 0 < R` using `hR'.trans hR'R`. Establish `h1 : 0 < 4 * (r + R') / (R' - r) ^ 2` using `div_pos (by linarith) (pow_pos (by linarith) 2)`. Establish `hlog : 0 < Real.log (R / R')` using `Real.log_pos ((one_lt_div hR').mpr hR'R)`. Establish `h2 : 0 < R' / (R * (R - R')) / Real.log (R / R')` using `div_pos (div_pos hR' (mul_pos hR (by linarith))) hlog`.

Unfold `locC`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma locC_pos {r R' R : ℝ} (hr : 0 < r) (hrR' : r < R') (hR'R : R' < R) : 0 < locC r R' R := by
  have hR' : 0 < R' := hr.trans hrR'
  have hR : 0 < R := hR'.trans hR'R
  have h1 : 0 < 4 * (r + R') / (R' - r) ^ 2 :=
    div_pos (by linarith) (pow_pos (by linarith) 2)
  have hlog : 0 < Real.log (R / R') := Real.log_pos ((one_lt_div hR').mpr hR'R)
  have h2 : 0 < R' / (R * (R - R')) / Real.log (R / R') :=
    div_pos (div_pos hR' (mul_pos hR (by linarith))) hlog
  unfold locC
  linarith

section core

variable {r R' R M : ℝ} {f h : ℂ → ℂ} {s₀ : ℂ} {Z : Finset ℂ} {m : ℂ → ℕ}

def gfun (s₀ : ℂ) (R : ℝ) (Z : Finset ℂ) (m : ℂ → ℕ) (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  (∏ ρ ∈ Z, (refl s₀ R ρ z) ^ (m ρ)) * h z

/- English proof (translation)
Establish `e : gfun s₀ R Z m h = fun z => (∏ ρ ∈ Z, refl s₀ R ρ z ^ m ρ) * h z` using `rfl`. Rewrite using `[e]`. Use `DifferentiableOn.mul ?_ hh` and prove the remaining obligations. Establish `hd : Differentiable ℂ (fun z => ∏ ρ ∈ Z, refl s₀ R ρ z ^ m ρ)` using `by first`. Consider the case `exact Differentiable.finset_prod fun ρ _ => (differentiable_refl s₀ R ρ).pow (m ρ)`.

Consider the case `(have hbd := differentiable_refl s₀ R; fun_prop)`. Conclude with `hd.differentiableOn`.
-/
private theorem differentiableOn_gfun_of_differentiableOn {U : Set ℂ} (hh : DifferentiableOn ℂ h U) :
    DifferentiableOn ℂ (gfun s₀ R Z m h) U := by
  have e : gfun s₀ R Z m h = fun z => (∏ ρ ∈ Z, refl s₀ R ρ z ^ m ρ) * h z := rfl
  rw [e]
  refine DifferentiableOn.mul ?_ hh
  have hd : Differentiable ℂ (fun z => ∏ ρ ∈ Z, refl s₀ R ρ z ^ m ρ) := by
    first
      | exact Differentiable.finset_prod fun ρ _ => (differentiable_refl s₀ R ρ).pow (m ρ)
      | (have hbd := differentiable_refl s₀ R; fun_prop)
  exact hd.differentiableOn

/- English proof (translation)
Establish `hR : 0 < R` using `hR'.trans hR'R`. Take `⟨N, hN⟩ : ∃ N : ℕ, ∑ ρ ∈ Z, m ρ = N` from `⟨_, rfl⟩`. Establish `hs₀R' : s₀ ∈ closedBall s₀ R'` using `mem_closedBall_self hR'.le`. Establish `hs₀R : s₀ ∈ closedBall s₀ R` using `mem_closedBall_self hR.le`. Establish `hhs₀ : h s₀ ≠ 0` using `hh0 s₀ hs₀R'`.

Establish `hg₀ : gfun s₀ R Z m h s₀ = (R : ℂ) ^ N * h s₀`. Establish `hc : ∀ ρ ∈ Z, refl s₀ R ρ s₀ ^ m ρ = (R : ℂ) ^ m ρ` using `fun ρ _ => by`. Rewrite using `[refl_center hR]`. Simplify using `only [gfun]`. Rewrite using `[Finset.prod_congr rfl hc, Finset.prod_pow_eq_pow_sum, hN]`.

Establish `hg₀n : ‖gfun s₀ R Z m h s₀‖ = R ^ N * ‖h s₀‖`. Rewrite using `[hg₀, norm_mul, norm_pow]`. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg hR.le]`. Establish `hf₀ : ‖f s₀‖ ≤ R' ^ N * ‖h s₀‖`. Rewrite using `[hfac s₀ hs₀R, norm_mul, norm_prod]`.

Use `mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod (fun ρ _ => by positivity) fun ρ hρ => ?_` and prove the remaining obligations. Establish `hρ' : ρ ∈ closedBall s₀ R'` using `((hZ ρ).1 hρ).1`. Rewrite `hρ'` using `[mem_closedBall, dist_eq_norm]`.

Rewrite using `[norm_sub_rev]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) hρ' _`. Use `_ = R' ^ N := by rw [Finset.prod_pow_eq_pow_sum, hN]`. Establish `hsphere : ∀ z ∈ sphere s₀ R, ‖gfun s₀ R Z m h z‖ = ‖f z‖`. Introduce `z hz`.

Rewrite using `[hfac z (sphere_subset_closedBall hz)]`. Simplify using `only [gfun, norm_mul, norm_prod, norm_pow, norm_refl_sphere hR hz]`. Establish `hdc : DiffContOnCl ℂ (gfun s₀ R Z m h) (ball s₀ R)`. Apply `DifferentiableOn.diffContOnCl` to reduce the goal to its premises. Rewrite using `[closure_ball s₀ hR.ne']`.

Conclude with `differentiableOn_gfun_of_differentiableOn hh`. Establish `hmax : ∀ z ∈ closedBall s₀ R, ‖gfun s₀ R Z m h z‖ ≤ Real.exp M * (R' ^ N * ‖h s₀‖)`. Introduce `z hz`. Use `Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc ?_ (by rwa [closure_ball s₀ hR.ne'])` and prove the remaining obligations. Introduce `w hw`.

Rewrite `hw` using `[frontier_ball s₀ hR.ne']`. Rewrite using `[hsphere w hw]`. Conclude with `(hb w (sphere_subset_closedBall hw)).trans (mul_le_mul_of_nonneg_left hf₀ (Real.exp_pos M).le)`. Establish `hkey : R ^ N ≤ Real.exp M * R' ^ N`. Establish `h1` using `hmax s₀ hs₀R`.

Rewrite `h1` using `[hg₀n, ← mul_assoc]`. Conclude with `le_of_mul_le_mul_right h1 (norm_pos_iff.mpr hhs₀)`. Use `⟨fun z hz => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hg₀n]`. Use `(hmax z hz).trans ?_` and prove the remaining obligations.

Establish `hp : R' ^ N ≤ R ^ N` using `pow_le_pow_left₀ hR'.le hR'R.le N`. Conclude with `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (norm_nonneg _)) (Real.exp_pos M).le`. Rewrite using `[hN]`. Establish `hl` using `Real.log_le_log (pow_pos hR N) hkey`. Rewrite `hl` using `[Real.log_mul (Real.exp_pos M).ne' (pow_pos hR' N).ne', Real.log_exp, Real.log_pow, Real.log_pow]`.

Rewrite using `[Real.log_div hR.ne' hR'.ne', mul_sub]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma gfun_bounds (hR' : 0 < R') (hR'R : R' < R)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ closedBall s₀ R' ∧ f ρ = 0))
    (hh : DifferentiableOn ℂ h (closedBall s₀ R)) (hh0 : ∀ z ∈ closedBall s₀ R', h z ≠ 0)
    (hfac : ∀ z ∈ closedBall s₀ R, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z)
    (hb : ∀ s ∈ closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) :
    (∀ z ∈ closedBall s₀ R, ‖gfun s₀ R Z m h z‖ ≤ Real.exp M * ‖gfun s₀ R Z m h s₀‖) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) * Real.log (R / R') ≤ M := by
  have hR : 0 < R := hR'.trans hR'R
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∑ ρ ∈ Z, m ρ = N := ⟨_, rfl⟩
  have hs₀R' : s₀ ∈ closedBall s₀ R' := mem_closedBall_self hR'.le
  have hs₀R : s₀ ∈ closedBall s₀ R := mem_closedBall_self hR.le
  have hhs₀ : h s₀ ≠ 0 := hh0 s₀ hs₀R'
  have hg₀ : gfun s₀ R Z m h s₀ = (R : ℂ) ^ N * h s₀ := by
    have hc : ∀ ρ ∈ Z, refl s₀ R ρ s₀ ^ m ρ = (R : ℂ) ^ m ρ := fun ρ _ => by
      rw [refl_center hR]
    simp only [gfun]
    rw [Finset.prod_congr rfl hc, Finset.prod_pow_eq_pow_sum, hN]
  have hg₀n : ‖gfun s₀ R Z m h s₀‖ = R ^ N * ‖h s₀‖ := by
    rw [hg₀, norm_mul, norm_pow]
    rw [Complex.norm_real, Real.norm_of_nonneg hR.le]
  have hf₀ : ‖f s₀‖ ≤ R' ^ N * ‖h s₀‖ := by
    rw [hfac s₀ hs₀R, norm_mul, norm_prod]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ∏ ρ ∈ Z, ‖(s₀ - ρ) ^ m ρ‖ = ∏ ρ ∈ Z, ‖s₀ - ρ‖ ^ m ρ := by simp only [norm_pow]
      _ ≤ ∏ ρ ∈ Z, R' ^ m ρ := by
        refine Finset.prod_le_prod (fun ρ _ => by positivity) fun ρ hρ => ?_
        have hρ' : ρ ∈ closedBall s₀ R' := ((hZ ρ).1 hρ).1
        rw [mem_closedBall, dist_eq_norm] at hρ'
        rw [norm_sub_rev]
        exact pow_le_pow_left₀ (norm_nonneg _) hρ' _
      _ = R' ^ N := by rw [Finset.prod_pow_eq_pow_sum, hN]
  have hsphere : ∀ z ∈ sphere s₀ R, ‖gfun s₀ R Z m h z‖ = ‖f z‖ := by
    intro z hz
    rw [hfac z (sphere_subset_closedBall hz)]
    simp only [gfun, norm_mul, norm_prod, norm_pow, norm_refl_sphere hR hz]
  have hdc : DiffContOnCl ℂ (gfun s₀ R Z m h) (ball s₀ R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s₀ hR.ne']
    exact differentiableOn_gfun_of_differentiableOn hh
  have hmax : ∀ z ∈ closedBall s₀ R,
      ‖gfun s₀ R Z m h z‖ ≤ Real.exp M * (R' ^ N * ‖h s₀‖) := by
    intro z hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc ?_
      (by rwa [closure_ball s₀ hR.ne'])
    intro w hw
    rw [frontier_ball s₀ hR.ne'] at hw
    rw [hsphere w hw]
    exact (hb w (sphere_subset_closedBall hw)).trans
      (mul_le_mul_of_nonneg_left hf₀ (Real.exp_pos M).le)
  have hkey : R ^ N ≤ Real.exp M * R' ^ N := by
    have h1 := hmax s₀ hs₀R
    rw [hg₀n, ← mul_assoc] at h1
    exact le_of_mul_le_mul_right h1 (norm_pos_iff.mpr hhs₀)
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [hg₀n]
    refine (hmax z hz).trans ?_
    have hp : R' ^ N ≤ R ^ N := pow_le_pow_left₀ hR'.le hR'R.le N
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
      (Real.exp_pos M).le
  · rw [hN]
    have hl := Real.log_le_log (pow_pos hR N) hkey
    rw [Real.log_mul (Real.exp_pos M).ne' (pow_pos hR' N).ne', Real.log_exp, Real.log_pow,
      Real.log_pow] at hl
    rw [Real.log_div hR.ne' hR'.ne', mul_sub]
    linarith

/- English proof (translation)
Introduce `s hs hfs`. Establish `hR' : 0 < R'` using `hr.trans hrR'`. Establish `hR : 0 < R` using `hR'.trans hR'R`. Take `⟨hg, hN⟩` from `gfun_bounds hR' hR'R hZ hh hh0 hfac hb`. Establish `hsR' : s ∈ closedBall s₀ R'` using `closedBall_subset_closedBall hrR'.le hs`.

Establish `hsball : s ∈ ball s₀ R` using `closedBall_subset_ball (hrR'.trans hR'R) hs`. Establish `hsR : s ∈ closedBall s₀ R` using `ball_subset_closedBall hsball`. Establish `hnhds : closedBall s₀ R ∈ 𝓝 s` using `Filter.mem_of_superset (isOpen_ball.mem_nhds hsball) ball_subset_closedBall`. Establish `hhs : h s ≠ 0` using `hh0 s hsR'`. Establish `hhd : DifferentiableAt ℂ h s` using `hh.differentiableAt hnhds`.

Establish `hρs : ∀ ρ ∈ Z, s - ρ ≠ 0`. Introduce `ρ hρ h0`. Establish `hsρ : s = ρ` using `sub_eq_zero.mp h0`. Conclude with `hfs (by rw [hsρ]; exact ((hZ ρ).1 hρ).2)`. Establish `hfeq : f =ᶠ[𝓝 s] fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z` using `Filter.eventually_of_mem hnhds fun z hz => hfac z hz`.

Establish `hlf : logDeriv f s = (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) + logDeriv h s`. Establish `e1 : logDeriv f s = logDeriv (fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z) s`. Rewrite using `[logDeriv_apply, logDeriv_apply, hfeq.deriv_eq, hfeq.eq_of_nhds]`. Rewrite using `[e1]`. Use `(logDeriv_prod_pow_mul (φ := fun ρ z => z - ρ) (h := h) hρs (fun ρ _ => by fun_prop) hhs hhd).trans ?_` and prove the remaining obligations.

Use `congr 1`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Use `show (m ρ : ℂ) * logDeriv (fun z => z - ρ) s = (m ρ : ℂ) / (s - ρ)`. Simplify using `only [logDeriv_apply, deriv_sub_const, deriv_id'']`. Expand and normalize the polynomial expressions, which then agree.

Establish `hBne : ∀ z ∈ closedBall s₀ R, ∀ ρ ∈ Z, refl s₀ R ρ z ≠ 0`. Introduce `z hz ρ hρ h0`. Establish `h1` using `le_norm_refl (R' := R') hR ((hZ ρ).1 hρ).1 hz`. Rewrite `h1` using `[h0, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlg : logDeriv (gfun s₀ R Z m h) s = (∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s) + logDeriv h s` using `logDeriv_prod_pow_mul (φ := fun ρ => refl s₀ R ρ) (fun ρ hρ => hBne s hsR ρ hρ) (fun ρ _ => (differentiable_refl s₀ R ρ).differentiableAt) hhs hhd`. Establish `hsub : ball s₀ R' ⊆ closedBall s₀ R` using `ball_subset_closedBall.trans (closedBall_subset_closedBall hR'R.le)`. Establish `hgne : ∀ z ∈ ball s₀ R', gfun s₀ R Z m h z ≠ 0`. Introduce `z hz`. Simplify using `only [gfun]`.

Conclude with `mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hBne z (hsub hz) ρ hρ)) (hh0 z (ball_subset_closedBall hz))`. Establish `hLg` using `logDeriv_bound_of_zero_free hDL hr hrR' hM (differentiableOn_gfun_of_differentiableOn (hh.mono hsub)) hgne (fun z hz => hg z (hsub hz)) s hs`. Establish `hLg' : ‖logDeriv (gfun s₀ R Z m h) s‖ ≤ 4 * (r + R') / (R' - r) ^ 2 * M`. Rewrite using `[logDeriv_apply]`. Conclude with `hLg`.

Establish `hK : 0 ≤ R' / (R * (R - R'))` using `div_nonneg hR'.le (mul_pos hR (by linarith)).le`. Establish `hlog : 0 < Real.log (R / R')` using `Real.log_pos ((one_lt_div hR').mpr hR'R)`. Establish `hNle : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ M / Real.log (R / R')`. Conclude with `(le_div_iff₀ hlog).mpr hN`. Establish `hsumB : ‖∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖ ≤ R' / (R * (R - R')) / Real.log (R / R') * M`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun ρ hρ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Establish `hn : ‖(m ρ : ℂ)‖ = (m ρ : ℝ)`. Conclude with `Complex.norm_natCast _`.

Rewrite using `[hn]`. Conclude with `mul_le_mul_of_nonneg_left (norm_logDeriv_refl_le hR'R hR ((hZ ρ).1 hρ).1 hsR) (Nat.cast_nonneg _)`. Use `_ = ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) * (R' / (R * (R - R'))) := by`. Rewrite using `[Nat.cast_sum, Finset.sum_mul]`. Use `_ ≤ M / Real.log (R / R') * (R' / (R * (R - R'))) := mul_le_mul_of_nonneg_right hNle hK`.

Use `_ = R' / (R * (R - R')) / Real.log (R / R') * M := by ring`. Establish `hdiff : logDeriv f s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) = logDeriv (gfun s₀ R Z m h) s - ∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s`. Rewrite using `[hlf, hlg]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hdiff]`.

Combine the equalities or inequalities in the displayed calculation. Unfold `locC`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem core (hDL : PI.DiscLog) (hr : 0 < r) (hrR' : r < R') (hR'R : R' < R) (hM : 0 < M)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ closedBall s₀ R' ∧ f ρ = 0))
    (hh : DifferentiableOn ℂ h (closedBall s₀ R)) (hh0 : ∀ z ∈ closedBall s₀ R', h z ≠ 0)
    (hfac : ∀ z ∈ closedBall s₀ R, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z)
    (hb : ∀ s ∈ closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) :
    ∀ s ∈ closedBall s₀ r, f s ≠ 0 →
      ‖logDeriv f s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ locC r R' R * M := by
  intro s hs hfs
  have hR' : 0 < R' := hr.trans hrR'
  have hR : 0 < R := hR'.trans hR'R
  obtain ⟨hg, hN⟩ := gfun_bounds hR' hR'R hZ hh hh0 hfac hb
  have hsR' : s ∈ closedBall s₀ R' := closedBall_subset_closedBall hrR'.le hs
  have hsball : s ∈ ball s₀ R := closedBall_subset_ball (hrR'.trans hR'R) hs
  have hsR : s ∈ closedBall s₀ R := ball_subset_closedBall hsball
  have hnhds : closedBall s₀ R ∈ 𝓝 s :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hsball) ball_subset_closedBall
  have hhs : h s ≠ 0 := hh0 s hsR'
  have hhd : DifferentiableAt ℂ h s := hh.differentiableAt hnhds
  have hρs : ∀ ρ ∈ Z, s - ρ ≠ 0 := by
    intro ρ hρ h0
    have hsρ : s = ρ := sub_eq_zero.mp h0
    exact hfs (by rw [hsρ]; exact ((hZ ρ).1 hρ).2)
  have hfeq : f =ᶠ[𝓝 s] fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z :=
    Filter.eventually_of_mem hnhds fun z hz => hfac z hz
  have hlf : logDeriv f s = (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) + logDeriv h s := by
    have e1 : logDeriv f s = logDeriv (fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z) s := by
      rw [logDeriv_apply, logDeriv_apply, hfeq.deriv_eq, hfeq.eq_of_nhds]
    rw [e1]
    refine (logDeriv_prod_pow_mul (φ := fun ρ z => z - ρ) (h := h) hρs
      (fun ρ _ => by fun_prop) hhs hhd).trans ?_
    congr 1
    refine Finset.sum_congr rfl fun ρ _ => ?_
    show (m ρ : ℂ) * logDeriv (fun z => z - ρ) s = (m ρ : ℂ) / (s - ρ)
    simp only [logDeriv_apply, deriv_sub_const, deriv_id'']
    ring
  have hBne : ∀ z ∈ closedBall s₀ R, ∀ ρ ∈ Z, refl s₀ R ρ z ≠ 0 := by
    intro z hz ρ hρ h0
    have h1 := le_norm_refl (R' := R') hR ((hZ ρ).1 hρ).1 hz
    rw [h0, norm_zero] at h1
    linarith
  have hlg : logDeriv (gfun s₀ R Z m h) s =
      (∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s) + logDeriv h s :=
    logDeriv_prod_pow_mul (φ := fun ρ => refl s₀ R ρ) (fun ρ hρ => hBne s hsR ρ hρ)
      (fun ρ _ => (differentiable_refl s₀ R ρ).differentiableAt) hhs hhd
  have hsub : ball s₀ R' ⊆ closedBall s₀ R :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hR'R.le)
  have hgne : ∀ z ∈ ball s₀ R', gfun s₀ R Z m h z ≠ 0 := by
    intro z hz
    simp only [gfun]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hBne z (hsub hz) ρ hρ))
      (hh0 z (ball_subset_closedBall hz))
  have hLg := logDeriv_bound_of_zero_free hDL hr hrR' hM
    (differentiableOn_gfun_of_differentiableOn (hh.mono hsub)) hgne (fun z hz => hg z (hsub hz)) s hs
  have hLg' : ‖logDeriv (gfun s₀ R Z m h) s‖ ≤ 4 * (r + R') / (R' - r) ^ 2 * M := by
    rw [logDeriv_apply]
    exact hLg
  have hK : 0 ≤ R' / (R * (R - R')) := div_nonneg hR'.le (mul_pos hR (by linarith)).le
  have hlog : 0 < Real.log (R / R') := Real.log_pos ((one_lt_div hR').mpr hR'R)
  have hNle : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ M / Real.log (R / R') := by
    exact (le_div_iff₀ hlog).mpr hN
  have hsumB : ‖∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖ ≤
      R' / (R * (R - R')) / Real.log (R / R') * M := by
    calc ‖∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖
        ≤ ∑ ρ ∈ Z, ‖(m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (R' / (R * (R - R'))) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rw [norm_mul]
          have hn : ‖(m ρ : ℂ)‖ = (m ρ : ℝ) := by
            exact Complex.norm_natCast _
          rw [hn]
          exact mul_le_mul_of_nonneg_left
            (norm_logDeriv_refl_le hR'R hR ((hZ ρ).1 hρ).1 hsR) (Nat.cast_nonneg _)
      _ = ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) * (R' / (R * (R - R'))) := by
          rw [Nat.cast_sum, Finset.sum_mul]
      _ ≤ M / Real.log (R / R') * (R' / (R * (R - R'))) :=
          mul_le_mul_of_nonneg_right hNle hK
      _ = R' / (R * (R - R')) / Real.log (R / R') * M := by ring
  have hdiff : logDeriv f s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) =
      logDeriv (gfun s₀ R Z m h) s -
        ∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s := by
    rw [hlf, hlg]
    ring
  rw [hdiff]
  calc _ ≤ ‖logDeriv (gfun s₀ R Z m h) s‖ +
        ‖∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖ := norm_sub_le _ _
    _ ≤ 4 * (r + R') / (R' - r) ^ 2 * M + R' / (R * (R - R')) / Real.log (R / R') * M :=
        add_le_add hLg' hsumB
    _ = locC r R' R * M := by
        unfold locC
        ring

end core

/- English proof (translation)
Establish `hR' : 0 < R'` using `hr.trans hrR'`. Establish `hfd : DifferentiableOn ℂ f (closedBall s₀ R)` using `hf.differentiableOn`. Take `⟨Z, m, h, hZ, -, hh, hh0, hfac⟩` from `hDF f s₀ R R' hR' hR'R hfd hf0`. Establish `hset : {ρ | ρ ∈ closedBall s₀ R' ∧ f ρ = 0} = (Z : Set ℂ)`. Use extensionality with `ρ`.

Simplify using `only [Set.mem_ofPred_eq, Finset.mem_coe]`. Conclude with `(hZ ρ).symm`. Establish `hord : ∀ ρ ∈ Z, analyticOrderNatAt f ρ = m ρ`. Introduce `ρ hρ`. Establish `hρR : ρ ∈ ball s₀ R` using `closedBall_subset_ball hR'R ((hZ ρ).1 hρ).1`.

Conclude with `order_eq_of_factor hρ (isOpen_ball.mem_nhds hρR) (hf ρ (ball_subset_closedBall hρR)) (hh.mono ball_subset_closedBall) (hh0 ρ ((hZ ρ).1 hρ).1) fun z hz => hfac z (ball_subset_closedBall hz)`. Use `⟨by rw [hset]; exact Z.finite_toSet, ?_⟩` and prove the remaining obligations. Introduce `s hs hfs`. Establish `hsum : ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ) = ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)` using `Finset.sum_congr rfl fun ρ hρ => by rw [hord ρ hρ]`. Rewrite using `[hset, finsum_mem_coe_finset, hsum]`.

Establish `hC : 0 < locC r R' R` using `locC_pos hr hrR' hR'R`. Use `le_of_forall_pos_le_add fun ε hε => ?_` and prove the remaining obligations. Establish `hεC : 0 < ε / locC r R' R` using `div_pos hε hC`. Establish `hM' : 0 < M + ε / locC r R' R` using `add_pos_of_nonneg_of_pos hM hεC`. Establish `hb' : ∀ z ∈ closedBall s₀ R, ‖f z‖ ≤ Real.exp (M + ε / locC r R' R) * ‖f s₀‖` using `fun z hz => (hb z hz).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (norm_nonneg _))`.

Establish `key` using `core hDL hr hrR' hR'R hM' hZ hh hh0 hfac hb' s hs hfs`. Establish `hCε : locC r R' R * (ε / locC r R' R) = ε`. Conclude with `mul_div_cancel₀ ε hC.ne'`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem local_abstract (hDF : PI.DiscFactor) (hDL : PI.DiscLog) {r R' R : ℝ} (hr : 0 < r)
    (hrR' : r < R') (hR'R : R' < R) (f : ℂ → ℂ) (s₀ : ℂ) (M : ℝ)
    (hf : AnalyticOnNhd ℂ f (closedBall s₀ R)) (hf0 : f s₀ ≠ 0) (hM : 0 ≤ M)
    (hb : ∀ s ∈ closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) :
    ({ρ | ρ ∈ closedBall s₀ R' ∧ f ρ = 0}).Finite ∧
      ∀ s ∈ closedBall s₀ r, f s ≠ 0 →
        ‖logDeriv f s - ∑ᶠ ρ ∈ {ρ | ρ ∈ closedBall s₀ R' ∧ f ρ = 0},
            (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤ locC r R' R * M := by
  have hR' : 0 < R' := hr.trans hrR'
  have hfd : DifferentiableOn ℂ f (closedBall s₀ R) := hf.differentiableOn
  obtain ⟨Z, m, h, hZ, -, hh, hh0, hfac⟩ := hDF f s₀ R R' hR' hR'R hfd hf0
  have hset : {ρ | ρ ∈ closedBall s₀ R' ∧ f ρ = 0} = (Z : Set ℂ) := by
    ext ρ
    simp only [Set.mem_ofPred_eq, Finset.mem_coe]
    exact (hZ ρ).symm
  have hord : ∀ ρ ∈ Z, analyticOrderNatAt f ρ = m ρ := by
    intro ρ hρ
    have hρR : ρ ∈ ball s₀ R := closedBall_subset_ball hR'R ((hZ ρ).1 hρ).1
    exact order_eq_of_factor hρ (isOpen_ball.mem_nhds hρR)
      (hf ρ (ball_subset_closedBall hρR)) (hh.mono ball_subset_closedBall)
      (hh0 ρ ((hZ ρ).1 hρ).1) fun z hz => hfac z (ball_subset_closedBall hz)
  refine ⟨by rw [hset]; exact Z.finite_toSet, ?_⟩
  intro s hs hfs
  have hsum : ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ) = ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) :=
    Finset.sum_congr rfl fun ρ hρ => by rw [hord ρ hρ]
  rw [hset, finsum_mem_coe_finset, hsum]
  have hC : 0 < locC r R' R := locC_pos hr hrR' hR'R
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hεC : 0 < ε / locC r R' R := div_pos hε hC
  have hM' : 0 < M + ε / locC r R' R := add_pos_of_nonneg_of_pos hM hεC
  have hb' : ∀ z ∈ closedBall s₀ R,
      ‖f z‖ ≤ Real.exp (M + ε / locC r R' R) * ‖f s₀‖ := fun z hz =>
    (hb z hz).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (norm_nonneg _))
  have key := core hDL hr hrR' hR'R hM' hZ hh hh0 hfac hb' s hs hfs
  have hCε : locC r R' R * (ε / locC r R' R) = ε := by
    exact mul_div_cancel₀ ε hC.ne'
  calc _ ≤ locC r R' R * (M + ε / locC r R' R) := key
    _ = locC r R' R * M + ε := by rw [mul_add, hCε]

end PI.EF.Loc
