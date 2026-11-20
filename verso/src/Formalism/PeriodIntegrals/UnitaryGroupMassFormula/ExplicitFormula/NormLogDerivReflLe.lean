import Mathlib

noncomputable section

namespace PI.EF.Loc

open Complex Metric Set Filter Topology ComplexConjugate

def refl (s₀ : ℂ) (R : ℝ) (ρ z : ℂ) : ℂ := ((R : ℂ) ^ 2 - conj (ρ - s₀) * (z - s₀)) / R

/- English proof (translation)
Establish `hw : ‖z - s₀‖ = R` using `by rwa [mem_sphere_iff_norm] at hz`. Establish `hR2 : (R : ℂ) ^ 2 = (z - s₀) * conj (z - s₀)`. Rewrite using `[mul_conj, normSq_eq_norm_sq, hw]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hk : (z - s₀) * conj (z - s₀) - conj (ρ - s₀) * (z - s₀) = (z - s₀) * conj (z - ρ)`. Simplify using `only [map_sub]`. Expand and normalize the polynomial expressions, which then agree. Unfold `refl`. Rewrite using `[hR2, hk, norm_div, norm_mul, Complex.norm_conj, hw, Complex.norm_real, Real.norm_of_nonneg hR.le]`.

Clear the denominators using the available nonvanishing facts.
-/
lemma norm_refl_sphere {s₀ ρ z : ℂ} {R : ℝ} (hR : 0 < R) (hz : z ∈ sphere s₀ R) :
    ‖refl s₀ R ρ z‖ = ‖z - ρ‖ := by
  have hw : ‖z - s₀‖ = R := by rwa [mem_sphere_iff_norm] at hz
  have hR2 : (R : ℂ) ^ 2 = (z - s₀) * conj (z - s₀) := by
    rw [mul_conj, normSq_eq_norm_sq, hw]
    push_cast
    ring
  have hk : (z - s₀) * conj (z - s₀) - conj (ρ - s₀) * (z - s₀) = (z - s₀) * conj (z - ρ) := by
    simp only [map_sub]
    ring
  unfold refl
  rw [hR2, hk, norm_div, norm_mul, Complex.norm_conj, hw, Complex.norm_real, Real.norm_of_nonneg hR.le]
  field_simp

/- English proof (translation)
Establish `ha : ‖ρ - s₀‖ ≤ R'` using `by rwa [mem_closedBall, dist_eq_norm] at hρ`. Establish `hw : ‖z - s₀‖ ≤ R` using `by rwa [mem_closedBall, dist_eq_norm] at hz`. Unfold `refl`. Rewrite using `[norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, le_div_iff₀ hR]`. Establish `h1 : ‖(R : ℂ) ^ 2‖ = R ^ 2`.

Rewrite using `[norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le]`. Establish `h2 : ‖conj (ρ - s₀) * (z - s₀)‖ ≤ R' * R`. Rewrite using `[norm_mul, Complex.norm_conj]`. Conclude with `mul_le_mul ha hw (norm_nonneg _) ((norm_nonneg _).trans ha)`. Establish `h3` using `norm_sub_norm_le ((R : ℂ) ^ 2) (conj (ρ - s₀) * (z - s₀))`.

Rewrite `h3` using `[h1]`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma le_norm_refl {s₀ ρ z : ℂ} {R R' : ℝ} (hR : 0 < R) (hρ : ρ ∈ closedBall s₀ R')
    (hz : z ∈ closedBall s₀ R) : R - R' ≤ ‖refl s₀ R ρ z‖ := by
  have ha : ‖ρ - s₀‖ ≤ R' := by rwa [mem_closedBall, dist_eq_norm] at hρ
  have hw : ‖z - s₀‖ ≤ R := by rwa [mem_closedBall, dist_eq_norm] at hz
  unfold refl
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, le_div_iff₀ hR]
  have h1 : ‖(R : ℂ) ^ 2‖ = R ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have h2 : ‖conj (ρ - s₀) * (z - s₀)‖ ≤ R' * R := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul ha hw (norm_nonneg _) ((norm_nonneg _).trans ha)
  have h3 := norm_sub_norm_le ((R : ℂ) ^ 2) (conj (ρ - s₀) * (z - s₀))
  rw [h1] at h3
  nlinarith

/- English proof (translation)
Establish `h : (R : ℂ) ≠ 0` using `by exact_mod_cast hR.ne'`. Unfold `refl`. Rewrite using `[sub_self, mul_zero, sub_zero, pow_two, mul_div_assoc, div_self h, mul_one]`.
-/
lemma refl_center {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) : refl s₀ R ρ s₀ = R := by
  have h : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  unfold refl
  rw [sub_self, mul_zero, sub_zero, pow_two, mul_div_assoc, div_self h, mul_one]

/- English proof (translation)
The claim follows from `((((hasDerivAt_id' z).sub_const s₀).const_mul (conj (ρ - s₀))).const_sub ((R : ℂ) ^ 2)).div_const (R : ℂ)`.
-/
lemma hasDerivAt_refl (s₀ : ℂ) (R : ℝ) (ρ z : ℂ) :
    HasDerivAt (refl s₀ R ρ) (-(conj (ρ - s₀) * 1) / R) z :=
  ((((hasDerivAt_id' z).sub_const s₀).const_mul (conj (ρ - s₀))).const_sub ((R : ℂ) ^ 2)).div_const (R : ℂ)

/- English proof (translation)
Introduce `z` and use `(hasDerivAt_refl s₀ R ρ z).differentiableAt`.
-/
lemma differentiable_refl (s₀ : ℂ) (R : ℝ) (ρ : ℂ) : Differentiable ℂ (refl s₀ R ρ) :=
  fun z => (hasDerivAt_refl s₀ R ρ z).differentiableAt

/- English proof (translation)
Establish `hpos : 0 < R - R'` using `sub_pos.mpr hR'R`. Establish `hl` using `le_norm_refl hR hρ hz`. Establish `hn : 0 < ‖refl s₀ R ρ z‖` using `lt_of_lt_of_le hpos hl`. Establish `ha : ‖ρ - s₀‖ ≤ R'` using `by rwa [mem_closedBall, dist_eq_norm] at hρ`. Rewrite using `[logDeriv_apply, (hasDerivAt_refl s₀ R ρ z).deriv, norm_div, norm_div, norm_neg, mul_one, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hR.le, div_div, div_le_div_iff₀ (mul_pos hR hn) (mul_pos hR hpos)]`.

Establish `h4` using `mul_le_mul ha hl hpos.le ((norm_nonneg _).trans ha)`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma norm_logDeriv_refl_le {s₀ ρ z : ℂ} {R R' : ℝ} (hR'R : R' < R) (hR : 0 < R)
    (hρ : ρ ∈ closedBall s₀ R') (hz : z ∈ closedBall s₀ R) :
    ‖logDeriv (refl s₀ R ρ) z‖ ≤ R' / (R * (R - R')) := by
  have hpos : 0 < R - R' := sub_pos.mpr hR'R
  have hl := le_norm_refl hR hρ hz
  have hn : 0 < ‖refl s₀ R ρ z‖ := lt_of_lt_of_le hpos hl
  have ha : ‖ρ - s₀‖ ≤ R' := by rwa [mem_closedBall, dist_eq_norm] at hρ
  rw [logDeriv_apply, (hasDerivAt_refl s₀ R ρ z).deriv, norm_div, norm_div, norm_neg, mul_one,
    Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hR.le, div_div,
    div_le_div_iff₀ (mul_pos hR hn) (mul_pos hR hpos)]
  have h4 := mul_le_mul ha hl hpos.le ((norm_nonneg _).trans ha)
  nlinarith

/- English proof (translation)
Establish `hP : (∏ ρ ∈ Z, (φ ρ s) ^ (m ρ)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hφ ρ hρ)`. Establish `hPd : DifferentiableAt ℂ (fun z => ∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) s`. Establish `h5` using `DifferentiableAt.finset_prod (f := fun ρ z => (φ ρ z) ^ (m ρ)) (fun ρ hρ => (hφd ρ hρ).pow _)`. Rewrite `h5` using `[Finset.prod_fn]`. Then use the resulting hypothesis. Rewrite using `[logDeriv_mul (f := fun z => ∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) (g := h) (x := s) hP hh hPd hhd]`.

Use `congr 1`. Establish `h6` using `logDeriv_prod (f := fun ρ z => (φ ρ z) ^ (m ρ)) (s := Z) (x := s) (fun ρ hρ => pow_ne_zero _ (hφ ρ hρ)) (fun ρ hρ => (hφd ρ hρ).pow _)`. Rewrite using `[h6]`. Use `Finset.sum_congr rfl fun ρ hρ => ?_` and prove the remaining obligations. Conclude with `logDeriv_fun_pow (hφd ρ hρ) (m ρ)`.
-/
lemma logDeriv_prod_pow_mul {Z : Finset ℂ} {m : ℂ → ℕ} {φ : ℂ → ℂ → ℂ} {h : ℂ → ℂ} {s : ℂ}
    (hφ : ∀ ρ ∈ Z, φ ρ s ≠ 0) (hφd : ∀ ρ ∈ Z, DifferentiableAt ℂ (φ ρ) s) (hh : h s ≠ 0)
    (hhd : DifferentiableAt ℂ h s) :
    logDeriv (fun z => (∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) * h z) s =
      (∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (φ ρ) s) + logDeriv h s := by
  have hP : (∏ ρ ∈ Z, (φ ρ s) ^ (m ρ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hφ ρ hρ)
  have hPd : DifferentiableAt ℂ (fun z => ∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) s :=
    by
      have h5 := DifferentiableAt.finset_prod (f := fun ρ z => (φ ρ z) ^ (m ρ)) (fun ρ hρ => (hφd ρ hρ).pow _)
      rwa [Finset.prod_fn] at h5
  rw [logDeriv_mul (f := fun z => ∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) (g := h) (x := s) hP hh hPd hhd]
  congr 1
  have h6 := logDeriv_prod (f := fun ρ z => (φ ρ z) ^ (m ρ)) (s := Z) (x := s)
    (fun ρ hρ => pow_ne_zero _ (hφ ρ hρ)) (fun ρ hρ => (hφd ρ hρ).pow _)
  rw [h6]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  exact logDeriv_fun_pow (hφd ρ hρ) (m ρ)

/- English proof (translation)
Establish `hha : AnalyticAt ℂ h ρ` using `hh.analyticAt hU`. Establish `hg : AnalyticAt ℂ (fun z => (∏ ρ' ∈ Z.erase ρ, (z - ρ') ^ (m ρ')) * h z) ρ`. Establish `h7` using `Finset.analyticAt_prod (𝕜 := ℂ) (Z.erase ρ) (f := fun ρ' z => (z - ρ') ^ (m ρ')) (c := ρ) (fun ρ' _ => by fun_prop)`. Rewrite `h7` using `[Finset.prod_fn]`. Conclude with `h7.mul hha`.

Establish `hg0 : (∏ ρ' ∈ Z.erase ρ, (ρ - ρ') ^ (m ρ')) * h ρ ≠ 0` using `mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ' hρ' => pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hρ').symm)) hhρ`. Establish `hord : analyticOrderAt f ρ = (m ρ : ℕ∞)`. Rewrite using `[hf.analyticOrderAt_eq_natCast]`. Use `⟨_, hg, hg0, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hU] with z hz`.

Rewrite using `[hfac z hz, ← Finset.mul_prod_erase Z (fun ρ' => (z - ρ') ^ (m ρ')) hρ, smul_eq_mul, mul_assoc]`. Simplify using `[analyticOrderNatAt, hord]`.
-/
lemma order_eq_of_factor {f h : ℂ → ℂ} {Z : Finset ℂ} {m : ℂ → ℕ} {ρ : ℂ} (hρ : ρ ∈ Z) {U : Set ℂ}
    (hU : U ∈ 𝓝 ρ) (hf : AnalyticAt ℂ f ρ) (hh : DifferentiableOn ℂ h U) (hhρ : h ρ ≠ 0)
    (hfac : ∀ z ∈ U, f z = (∏ ρ' ∈ Z, (z - ρ') ^ (m ρ')) * h z) :
    analyticOrderNatAt f ρ = m ρ := by
  have hha : AnalyticAt ℂ h ρ := hh.analyticAt hU
  have hg : AnalyticAt ℂ (fun z => (∏ ρ' ∈ Z.erase ρ, (z - ρ') ^ (m ρ')) * h z) ρ :=
    by
      have h7 := Finset.analyticAt_prod (𝕜 := ℂ) (Z.erase ρ) (f := fun ρ' z => (z - ρ') ^ (m ρ')) (c := ρ)
        (fun ρ' _ => by fun_prop)
      rw [Finset.prod_fn] at h7
      exact h7.mul hha
  have hg0 : (∏ ρ' ∈ Z.erase ρ, (ρ - ρ') ^ (m ρ')) * h ρ ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ' hρ' =>
      pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hρ').symm)) hhρ
  have hord : analyticOrderAt f ρ = (m ρ : ℕ∞) := by
    rw [hf.analyticOrderAt_eq_natCast]
    refine ⟨_, hg, hg0, ?_⟩
    filter_upwards [hU] with z hz
    rw [hfac z hz, ← Finset.mul_prod_erase Z (fun ρ' => (z - ρ') ^ (m ρ')) hρ, smul_eq_mul, mul_assoc]
  simp [analyticOrderNatAt, hord]

end PI.EF.Loc
