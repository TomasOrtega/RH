import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOnGaussNormAcrisRadiusIcoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonomialLtOfBoundedIntervalEndsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisLocallyMonomialStatement

noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Conclude with `(Fact.out : l.Prime).one_lt` after adjusting the coercions.
-/
lemma one_lt_natCast_of_prime : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt

/- English proof (translation)
Establish `hL` using `one_lt_natCast_of_prime (l := l)`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← Real.rpow_neg_one]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)`. Conclude with `Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)`.
-/
lemma prime_rpow_neg_mem_Ico_inv_one {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    (l : ℝ)⁻¹ ≤ (l : ℝ) ^ (-r) ∧ (l : ℝ) ^ (-r) < 1 := by
  have hL := one_lt_natCast_of_prime (l := l)
  constructor
  · rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
  · exact Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)

/- English proof (translation)
Establish `hL` using `one_lt_natCast_of_prime (l := l)`. Establish `hL0 : (0 : ℝ) < l` using `by linarith`. Take `⟨a1, b1⟩` from `prime_rpow_neg_mem_Ico_inv_one (l := l) (by linarith : 0 < r₁) h2`. Take `⟨a2, b2⟩` from `prime_rpow_neg_mem_Ico_inv_one (l := l) h1 (by linarith)`. Establish `hm0 : 0 < t * r₁ + (1 - t) * r₂` using `by nlinarith`.

Establish `hm1 : t * r₁ + (1 - t) * r₂ ≤ 1` using `by nlinarith`. Take `⟨a0, b0⟩` from `prime_rpow_neg_mem_Ico_inv_one (l := l) hm0 hm1`. Establish `hle : (l : ℝ) ^ (-r₁) ≤ (l : ℝ) ^ (-r₂)` using `Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)`. Establish `key` using `GlobalTheory.T.gaussNormAcris_logConvex_in_radius l x _ _ t a1 hle b2 ht0 ht1`. Establish `heq : ((l : ℝ) ^ (-r₁)) ^ t * ((l : ℝ) ^ (-r₂)) ^ (1 - t) = (l : ℝ) ^ (-(t * r₁ + (1 - t) * r₂))`.

Rewrite using `[← Real.rpow_mul hL0.le, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[heq]`. Establish `p1` using `GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ a1 b1`.

Establish `p2` using `GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ a2 b2`. Establish `p0` using `GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ a0 b0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.logb_mul (Real.rpow_pos_of_pos p1 _).ne' (Real.rpow_pos_of_pos p2 _).ne', Real.logb_rpow_eq_mul_logb_of_pos p1, Real.logb_rpow_eq_mul_logb_of_pos p2]`.
-/
lemma logb_gaussNormAcrisRadius_convex {x : Formalism.Per.Acris l} (hx : x ≠ 0) {r₁ r₂ t : ℝ} (h1 : 0 < r₂) (h12 : r₂ ≤ r₁)
    (h2 : r₁ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.logb l (gC l ((l : ℝ) ^ (-(t * r₁ + (1 - t) * r₂))) x) ≤
      t * Real.logb l (gC l ((l : ℝ) ^ (-r₁)) x) + (1 - t) * Real.logb l (gC l ((l : ℝ) ^ (-r₂)) x) := by
  have hL := one_lt_natCast_of_prime (l := l)
  have hL0 : (0 : ℝ) < l := by linarith
  obtain ⟨a1, b1⟩ := prime_rpow_neg_mem_Ico_inv_one (l := l) (by linarith : 0 < r₁) h2
  obtain ⟨a2, b2⟩ := prime_rpow_neg_mem_Ico_inv_one (l := l) h1 (by linarith)
  have hm0 : 0 < t * r₁ + (1 - t) * r₂ := by nlinarith
  have hm1 : t * r₁ + (1 - t) * r₂ ≤ 1 := by nlinarith
  obtain ⟨a0, b0⟩ := prime_rpow_neg_mem_Ico_inv_one (l := l) hm0 hm1
  have hle : (l : ℝ) ^ (-r₁) ≤ (l : ℝ) ^ (-r₂) := Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
  have key := GlobalTheory.T.gaussNormAcris_logConvex_in_radius l x _ _ t a1 hle b2 ht0 ht1
  have heq : ((l : ℝ) ^ (-r₁)) ^ t * ((l : ℝ) ^ (-r₂)) ^ (1 - t) = (l : ℝ) ^ (-(t * r₁ + (1 - t) * r₂)) := by
    rw [← Real.rpow_mul hL0.le, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
    congr 1; ring
  rw [heq] at key
  have p1 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ a1 b1
  have p2 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ a2 b2
  have p0 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ a0 b0
  calc Real.logb l (gC l ((l : ℝ) ^ (-(t * r₁ + (1 - t) * r₂))) x)
      ≤ Real.logb l (gC l ((l : ℝ) ^ (-r₁)) x ^ t * gC l ((l : ℝ) ^ (-r₂)) x ^ (1 - t)) :=
        Real.logb_le_logb_of_le hL p0 key
    _ = t * Real.logb l (gC l ((l : ℝ) ^ (-r₁)) x) + (1 - t) * Real.logb l (gC l ((l : ℝ) ^ (-r₂)) x) := by
        rw [Real.logb_mul (Real.rpow_pos_of_pos p1 _).ne' (Real.rpow_pos_of_pos p2 _).ne',
          Real.logb_rpow_eq_mul_logb_of_pos p1, Real.logb_rpow_eq_mul_logb_of_pos p2]

/- English proof (translation)
Use `⟨convex_Ioc 0 1, ?_⟩` and prove the remaining obligations. Introduce `r₁ hr₁ r₂ hr₂ a b ha hb hab`. Simplify using `only [vr, smul_eq_mul]`. Establish `hb' : b = 1 - a` using `by linarith`. Substitute `hb'` using the available equality.

Break down `le_total r₂ r₁ with h | h` into its components or cases. Use `logb_gaussNormAcrisRadius_convex hx hr₂.1 h hr₁.2 ha (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `logb_gaussNormAcrisRadius_convex hx hr₁.1 h hr₂.2 (t := 1 - a) (by linarith) (by linarith)` as an intermediate fact. Establish `e : (1 - a) * r₂ + (1 - (1 - a)) * r₁ = a * r₁ + (1 - a) * r₂` using `by ring`.

Rewrite `this` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem vr_concaveOn_Ioc {x : Formalism.Per.Acris l} (hx : x ≠ 0) :
    ConcaveOn ℝ (Set.Ioc 0 1) (fun r => vr l r x) := by
  refine ⟨convex_Ioc 0 1, ?_⟩
  intro r₁ hr₁ r₂ hr₂ a b ha hb hab
  simp only [vr, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  rcases le_total r₂ r₁ with h | h
  · have := logb_gaussNormAcrisRadius_convex hx hr₂.1 h hr₁.2 ha (by linarith)
    linarith
  · have := logb_gaussNormAcrisRadius_convex hx hr₁.1 h hr₂.2 (t := 1 - a) (by linarith) (by linarith)
    have e : (1 - a) * r₂ + (1 - (1 - a)) * r₁ = a * r₁ + (1 - a) * r₂ := by ring
    rw [e] at this
    linarith

/- English proof (translation)
Establish `hL` using `one_lt_natCast_of_prime (l := l)`. Establish `hL0 : (0 : ℝ) < l` using `by linarith`. Establish `hmaps : Set.MapsTo (fun r : ℝ => (l : ℝ) ^ (-r)) (Set.Ioc 0 1) (Set.Ico (l : ℝ)⁻¹ 1)` using `fun r hr => prime_rpow_neg_mem_Ico_inv_one hr.1 hr.2`. Establish `hc1 : Continuous (fun r : ℝ => (l : ℝ) ^ (-r))` using `Continuous.rpow continuous_const continuous_neg (fun _ => Or.inl hL0.ne')`. Establish `hc2 : ContinuousOn (fun r : ℝ => gC l ((l : ℝ) ^ (-r)) x) (Set.Ioc 0 1)` using `(GlobalTheory.T.continuousOn_gaussNormAcrisRadius_Ico l x).comp hc1.continuousOn hmaps`.

Establish `hpos : ∀ r ∈ Set.Ioc (0 : ℝ) 1, gC l ((l : ℝ) ^ (-r)) x ≠ 0` using `fun r hr => (GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ (prime_rpow_neg_mem_Ico_inv_one hr.1 hr.2).1 (prime_rpow_neg_mem_Ico_inv_one hr.1 hr.2).2).ne'`. Simplify using `only [vr, Real.logb]`. Conclude with `((hc2.log hpos).div_const _).neg`.
-/
theorem vr_continuousOn_Ioc {x : Formalism.Per.Acris l} (hx : x ≠ 0) :
    ContinuousOn (fun r => vr l r x) (Set.Ioc 0 1) := by
  have hL := one_lt_natCast_of_prime (l := l)
  have hL0 : (0 : ℝ) < l := by linarith
  have hmaps : Set.MapsTo (fun r : ℝ => (l : ℝ) ^ (-r)) (Set.Ioc 0 1) (Set.Ico (l : ℝ)⁻¹ 1) :=
    fun r hr => prime_rpow_neg_mem_Ico_inv_one hr.1 hr.2
  have hc1 : Continuous (fun r : ℝ => (l : ℝ) ^ (-r)) :=
    Continuous.rpow continuous_const continuous_neg (fun _ => Or.inl hL0.ne')
  have hc2 : ContinuousOn (fun r : ℝ => gC l ((l : ℝ) ^ (-r)) x) (Set.Ioc 0 1) :=
    (GlobalTheory.T.continuousOn_gaussNormAcrisRadius_Ico l x).comp hc1.continuousOn hmaps
  have hpos : ∀ r ∈ Set.Ioc (0 : ℝ) 1, gC l ((l : ℝ) ^ (-r)) x ≠ 0 := fun r hr =>
    (GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ (prime_rpow_neg_mem_Ico_inv_one hr.1 hr.2).1 (prime_rpow_neg_mem_Ico_inv_one hr.1 hr.2).2).ne'
  simp only [vr, Real.logb]
  exact ((hc2.log hpos).div_const _).neg

/- English proof (translation)
Introduce `r hr`. Establish `hL` using `one_lt_natCast_of_prime (l := l)`. Establish `hL0 : (0 : ℝ) < l` using `by linarith`. Take `⟨a, b⟩` from `prime_rpow_neg_mem_Ico_inv_one (l := l) hr.1 hr.2.le`. Establish `hlt : (l : ℝ)⁻¹ < (l : ℝ) ^ (-r)`.

Rewrite using `[← Real.rpow_neg_one]; exact Real.rpow_lt_rpow_of_exponent_lt hL (by linarith [hr.2])`. Take `⟨c, k, ρ₁, hc, hρ₁, hρ₁r, hmon⟩` from `(GlobalTheory.T.gaussNormAcris_locally_monomial l x hx _ a b).2 hlt`. Establish `hρ₁0 : 0 < ρ₁` using `lt_of_lt_of_le (inv_pos.mpr hL0) hρ₁`. Establish `hsr : r < -Real.logb l ρ₁`. Use `Real.logb_lt_logb hL hρ₁0 hρ₁r` as an intermediate fact.

Rewrite `this` using `[Real.logb_rpow hL0 hL.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hρs : ρ₁ = (l : ℝ) ^ (-(-Real.logb l ρ₁))`. Rewrite using `[neg_neg, Real.rpow_logb hL0 hL.ne' hρ₁0]`. Establish `hlogl : Real.log l ≠ 0` using `(Real.log_pos hL).ne'`.

Establish `formula : ∀ t, r ≤ t → t ≤ -Real.logb l ρ₁ → vr l t x = -Real.logb l c + k * t`. Introduce `t ht1 ht2`. Establish `hmem : (l : ℝ) ^ (-t) ∈ Set.Icc ρ₁ ((l : ℝ) ^ (-r))`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hρs]; exact Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)`.

Conclude with `Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)`. Simplify using `only [vr]`. Rewrite using `[hmon _ hmem]`. Simplify using `only [Real.logb]`. Rewrite using `[Real.log_mul hc.ne' (zpow_ne_zero _ (Real.rpow_pos_of_pos hL0 _).ne'), Real.log_zpow, Real.log_rpow hL0]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `⟨k, min (-Real.logb l ρ₁ - r) (1 - r), lt_min (by linarith) (by linarith [hr.2]), by linarith [min_le_right (-Real.logb l ρ₁ - r) (1 - r)], ?_⟩` and prove the remaining obligations. Introduce `t ht`. Establish `hs1 : r + min (-Real.logb l ρ₁ - r) (1 - r) ≤ -Real.logb l ρ₁`.

Combine the linear relations using `[min_le_left (-Real.logb l ρ₁ - r) (1 - r)]`. Rewrite using `[formula t ht.1 (ht.2.trans hs1), formula r le_rfl hsr.le]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vr_right_affine {x : Formalism.Per.Acris l} (hx : x ≠ 0) :
    ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ (k : ℤ) (δ : ℝ), 0 < δ ∧ r + δ ≤ 1 ∧
      ∀ t ∈ Set.Icc r (r + δ), vr l t x = vr l r x + k * (t - r) := by
  intro r hr
  have hL := one_lt_natCast_of_prime (l := l)
  have hL0 : (0 : ℝ) < l := by linarith
  obtain ⟨a, b⟩ := prime_rpow_neg_mem_Ico_inv_one (l := l) hr.1 hr.2.le
  have hlt : (l : ℝ)⁻¹ < (l : ℝ) ^ (-r) := by
    rw [← Real.rpow_neg_one]; exact Real.rpow_lt_rpow_of_exponent_lt hL (by linarith [hr.2])
  obtain ⟨c, k, ρ₁, hc, hρ₁, hρ₁r, hmon⟩ := (GlobalTheory.T.gaussNormAcris_locally_monomial l x hx _ a b).2 hlt
  have hρ₁0 : 0 < ρ₁ := lt_of_lt_of_le (inv_pos.mpr hL0) hρ₁
  have hsr : r < -Real.logb l ρ₁ := by
    have := Real.logb_lt_logb hL hρ₁0 hρ₁r
    rw [Real.logb_rpow hL0 hL.ne'] at this
    linarith
  have hρs : ρ₁ = (l : ℝ) ^ (-(-Real.logb l ρ₁)) := by
    rw [neg_neg, Real.rpow_logb hL0 hL.ne' hρ₁0]
  have hlogl : Real.log l ≠ 0 := (Real.log_pos hL).ne'
  have formula : ∀ t, r ≤ t → t ≤ -Real.logb l ρ₁ → vr l t x = -Real.logb l c + k * t := by
    intro t ht1 ht2
    have hmem : (l : ℝ) ^ (-t) ∈ Set.Icc ρ₁ ((l : ℝ) ^ (-r)) := by
      constructor
      · rw [hρs]; exact Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
      · exact Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
    simp only [vr]
    rw [hmon _ hmem]
    simp only [Real.logb]
    rw [Real.log_mul hc.ne' (zpow_ne_zero _ (Real.rpow_pos_of_pos hL0 _).ne'), Real.log_zpow,
      Real.log_rpow hL0]
    field_simp
    ring
  refine ⟨k, min (-Real.logb l ρ₁ - r) (1 - r), lt_min (by linarith) (by linarith [hr.2]),
    by linarith [min_le_right (-Real.logb l ρ₁ - r) (1 - r)], ?_⟩
  intro t ht
  have hs1 : r + min (-Real.logb l ρ₁ - r) (1 - r) ≤ -Real.logb l ρ₁ := by
    linarith [min_le_left (-Real.logb l ρ₁ - r) (1 - r)]
  rw [formula t ht.1 (ht.2.trans hs1), formula r le_rfl hsr.le]
  ring

/- English proof (translation)
Introduce `_ _ _ hx` and use `⟨vr_concaveOn_Ioc hx, vr_continuousOn_Ioc hx, vr_right_affine hx⟩`.
-/
theorem vr_concave_cont_rightSlope : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 →
    ConcaveOn ℝ (Set.Ioc 0 1) (fun r => vr l r x) ∧ ContinuousOn (fun r => vr l r x) (Set.Ioc 0 1) ∧
      ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ (k : ℤ) (δ : ℝ), 0 < δ ∧ r + δ ≤ 1 ∧
        ∀ t ∈ Set.Icc r (r + δ), vr l t x = vr l r x + k * (t - r) :=
  fun _ _ _ hx => ⟨vr_concaveOn_Ioc hx, vr_continuousOn_Ioc hx, vr_right_affine hx⟩

end GlobalTheory.PMon.Gauss

end
