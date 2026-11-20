import Formalism.HermitianCurvature.StatementE
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Herglotz

namespace Formalism.FourierDecayAlt.P.HLsc

open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz

variable {d : ℕ}

noncomputable def tp (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) (y : Fin d → ℝ) : ℂ :=
  ∑ σ ∈ B, c σ * ee y σ

/- English proof (translation)
Unfold `ee`. Use `fun_prop`.
-/
lemma continuous_ee (σ : Fin d → ℤ) : Continuous (fun y : Fin d → ℝ => ee y σ) := by
  unfold ee; fun_prop

/- English proof (translation)
Unfold `tp`. Conclude with `continuous_finsetSum _ (fun σ _ => continuous_const.mul (continuous_ee σ))`.
-/
lemma continuous_tp (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) : Continuous (tp B c) := by
  unfold tp
  exact continuous_finsetSum _ (fun σ _ => continuous_const.mul (continuous_ee σ))

/- English proof (translation)
Use `push_cast`. Rewrite using `[← Complex.mul_conj']`. Unfold `tp`. Rewrite using `[map_sum, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun σ' _ => ?_))` and prove the remaining obligations.

Rewrite using `[← ee_mul_conj, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma normSq_tp (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) (y : Fin d → ℝ) :
    ((‖tp B c y‖ ^ 2 : ℝ) : ℂ) =
      ∑ σ ∈ B, ∑ σ' ∈ B, ee y (σ - σ') * c σ * starRingEnd ℂ (c σ') := by
  push_cast
  rw [← Complex.mul_conj']
  unfold tp
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun σ' _ => ?_))
  rw [← ee_mul_conj, map_mul]
  ring

/- English proof (translation)
The claim follows from `hW.ofReal.mul_bdd (c := 1) (continuous_ee σ).aestronglyMeasurable (Eventually.of_forall (fun z => (norm_ee z σ).le))`.
-/
lemma integrable_mul_ee {W : (Fin d → ℝ) → ℝ} (hW : Integrable W) (σ : Fin d → ℤ) :
    Integrable (fun z => (W z : ℂ) * ee z σ) :=
  hW.ofReal.mul_bdd (c := 1) (continuous_ee σ).aestronglyMeasurable
    (Eventually.of_forall (fun z => (norm_ee z σ).le))

/- English proof (translation)
Rewrite using `[← integral_complex_ofReal]`. Establish `h1 : ∀ z, ((W z * ‖tp B c z‖ ^ 2 : ℝ) : ℂ) = ∑ σ ∈ B, ∑ σ' ∈ B, ((W z : ℂ) * ee z (σ - σ')) * (c σ * starRingEnd ℂ (c σ'))`. Introduce `z`. Rewrite using `[Complex.ofReal_mul, normSq_tp, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun σ' _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[h1]`. Rewrite using `[integral_finsetSum]`.

Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations. Rewrite using `[integral_finsetSum]`. Use `Finset.sum_congr rfl (fun σ' _ => ?_)` and prove the remaining obligations. Rewrite using `[integral_mul_const, mul_assoc]`. Introduce `σ' _`.

Conclude with `(integrable_mul_ee hW _).mul_const _`. Introduce `σ _`. Conclude with `integrable_finsetSum _ (fun σ' _ => (integrable_mul_ee hW _).mul_const _)`.
-/
lemma integral_mul_normSq_tp {W : (Fin d → ℝ) → ℝ} (hW : Integrable W)
    (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    ((∫ z, W z * ‖tp B c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ σ ∈ B, ∑ σ' ∈ B, (∫ z, (W z : ℂ) * ee z (σ - σ')) * c σ * starRingEnd ℂ (c σ') := by
  rw [← integral_complex_ofReal]
  have h1 : ∀ z, ((W z * ‖tp B c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ σ ∈ B, ∑ σ' ∈ B, ((W z : ℂ) * ee z (σ - σ')) * (c σ * starRingEnd ℂ (c σ')) := by
    intro z
    rw [Complex.ofReal_mul, normSq_tp, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ' _ => ?_)
    ring
  simp_rw [h1]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun σ' _ => ?_)
      rw [integral_mul_const, mul_assoc]
    · intro σ' _
      exact (integrable_mul_ee hW _).mul_const _
  · intro σ _
    exact integrable_finsetSum _ (fun σ' _ => (integrable_mul_ee hW _).mul_const _)

/- English proof (translation)
Rewrite using `[← (Equiv.subLeft σ).tsum_eq κ]`. Conclude with `((Equiv.subLeft σ).summable_iff.2 hκ).sum_le_tsum B (fun i _ => hκ0 _)`.
-/
lemma sum_sub_le_tsum {κ : (Fin d → ℤ) → ℝ} (hκ0 : ∀ σ, 0 ≤ κ σ) (hκ : Summable κ)
    (B : Finset (Fin d → ℤ)) (σ : Fin d → ℤ) :
    ∑ σ' ∈ B, κ (σ - σ') ≤ ∑' τ, κ τ := by
  rw [← (Equiv.subLeft σ).tsum_eq κ]
  exact ((Equiv.subLeft σ).summable_iff.2 hκ).sum_le_tsum B (fun i _ => hκ0 _)

/- English proof (translation)
Rewrite using `[← (Equiv.subRight σ').tsum_eq κ]`. Conclude with `((Equiv.subRight σ').summable_iff.2 hκ).sum_le_tsum B (fun i _ => hκ0 _)`.
-/
lemma sum_sub_le_tsum' {κ : (Fin d → ℤ) → ℝ} (hκ0 : ∀ σ, 0 ≤ κ σ) (hκ : Summable κ)
    (B : Finset (Fin d → ℤ)) (σ' : Fin d → ℤ) :
    ∑ σ ∈ B, κ (σ - σ') ≤ ∑' τ, κ τ := by
  rw [← (Equiv.subRight σ').tsum_eq κ]
  exact ((Equiv.subRight σ').summable_iff.2 hκ).sum_le_tsum B (fun i _ => hκ0 _)

/- English proof (translation)
Establish `h1 : ∑ σ ∈ B, ∑ σ' ∈ B, κ (σ - σ') * a σ * a σ' ≤ ∑ σ ∈ B, ∑ σ' ∈ B, (κ (σ - σ') * (a σ ^ 2 / 2) + κ (σ - σ') * (a σ' ^ 2 / 2))`. Use `Finset.sum_le_sum (fun σ _ => Finset.sum_le_sum (fun σ' _ => ?_))` and prove the remaining obligations. Use `hκ0 (σ - σ')` as an intermediate fact. Use polynomial arithmetic with `[mul_nonneg this (sq_nonneg (a σ - a σ'))]`. Use `h1.trans ?_` and prove the remaining obligations.

Repeatedly rewrite using `[Finset.sum_add_distrib]`. Establish `h2 : ∑ σ ∈ B, ∑ σ' ∈ B, κ (σ - σ') * (a σ ^ 2 / 2) ≤ ∑ σ ∈ B, (∑' τ, κ τ) * (a σ ^ 2 / 2)`. Use `Finset.sum_le_sum (fun σ _ => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul]`. Conclude with `mul_le_mul_of_nonneg_right (sum_sub_le_tsum hκ0 hκ B σ) (by positivity)`.

Establish `h3 : ∑ σ ∈ B, ∑ σ' ∈ B, κ (σ - σ') * (a σ' ^ 2 / 2) ≤ ∑ σ' ∈ B, (∑' τ, κ τ) * (a σ' ^ 2 / 2)`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_le_sum (fun σ' _ => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul]`. Conclude with `mul_le_mul_of_nonneg_right (sum_sub_le_tsum' hκ0 hκ B σ') (by positivity)`.

Use `(add_le_add h2 h3).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, ← mul_add, ← Finset.sum_add_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma schur {κ : (Fin d → ℤ) → ℝ} (hκ0 : ∀ σ, 0 ≤ κ σ) (hκ : Summable κ)
    (B : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℝ) :
    ∑ σ ∈ B, ∑ σ' ∈ B, κ (σ - σ') * a σ * a σ' ≤ (∑' τ, κ τ) * ∑ σ ∈ B, a σ ^ 2 := by
  have h1 : ∑ σ ∈ B, ∑ σ' ∈ B, κ (σ - σ') * a σ * a σ' ≤
      ∑ σ ∈ B, ∑ σ' ∈ B, (κ (σ - σ') * (a σ ^ 2 / 2) + κ (σ - σ') * (a σ' ^ 2 / 2)) := by
    refine Finset.sum_le_sum (fun σ _ => Finset.sum_le_sum (fun σ' _ => ?_))
    have := hκ0 (σ - σ')
    nlinarith [mul_nonneg this (sq_nonneg (a σ - a σ'))]
  refine h1.trans ?_
  simp_rw [Finset.sum_add_distrib]
  have h2 : ∑ σ ∈ B, ∑ σ' ∈ B, κ (σ - σ') * (a σ ^ 2 / 2) ≤
      ∑ σ ∈ B, (∑' τ, κ τ) * (a σ ^ 2 / 2) := by
    refine Finset.sum_le_sum (fun σ _ => ?_)
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_sub_le_tsum hκ0 hκ B σ) (by positivity)
  have h3 : ∑ σ ∈ B, ∑ σ' ∈ B, κ (σ - σ') * (a σ' ^ 2 / 2) ≤
      ∑ σ' ∈ B, (∑' τ, κ τ) * (a σ' ^ 2 / 2) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun σ' _ => ?_)
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_sub_le_tsum' hκ0 hκ B σ') (by positivity)
  refine (add_le_add h2 h3).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  ring

/- English proof (translation)
Establish `h1` using `integral_mul_normSq_tp hint B c`. Establish `h2` using `hPD B c`. Establish `h3 : (∑ σ ∈ B, ∑ σ' ∈ B, ((∫ z, (N z : ℂ) * ee z (σ - σ')) + A (σ - σ')) * c σ * starRingEnd ℂ (c σ')) = ((∫ z, N z * ‖tp B c z‖ ^ 2 : ℝ) : ℂ) + ∑ σ ∈ B, ∑ σ' ∈ B, A (σ - σ') * c σ * starRingEnd ℂ (c σ')`. Rewrite using `[h1, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun σ' _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `h4 : ∫ z, N z * ‖tp B c z‖ ^ 2 ≤ (∑ σ ∈ B, ∑ σ' ∈ B, ((∫ z, (N z : ℂ) * ee z (σ - σ')) + A (σ - σ')) * c σ * starRingEnd ℂ (c σ')).re`. Rewrite using `[h3, Complex.add_re, Complex.ofReal_re]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `h4.trans ((Complex.re_le_norm _).trans ?_)` and prove the remaining obligations. Use `le_trans ?_ (schur (fun σ => norm_nonneg _) hsum B (fun σ => ‖c σ‖))` and prove the remaining obligations. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum (fun σ _ => ?_))` and prove the remaining obligations. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum (fun σ' _ => ?_))` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_mul, RCLike.norm_conj]`.
-/
lemma key_upper {N : (Fin d → ℝ) → ℝ} {A : (Fin d → ℤ) → ℂ} (hint : Integrable N)
    (hPD : ∀ (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
        0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * starRingEnd ℂ (c σ')).re)
    (hsum : Summable (fun σ : Fin d → ℤ => ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖))
    (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    ∫ z, N z * ‖tp B c z‖ ^ 2 ≤
      (∑' σ : Fin d → ℤ, ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖) * ∑ σ ∈ B, ‖c σ‖ ^ 2 := by
  have h1 := integral_mul_normSq_tp hint B c
  have h2 := hPD B c
  have h3 : (∑ σ ∈ B, ∑ σ' ∈ B,
      ((∫ z, (N z : ℂ) * ee z (σ - σ')) + A (σ - σ')) * c σ * starRingEnd ℂ (c σ')) =
      ((∫ z, N z * ‖tp B c z‖ ^ 2 : ℝ) : ℂ) +
        ∑ σ ∈ B, ∑ σ' ∈ B, A (σ - σ') * c σ * starRingEnd ℂ (c σ') := by
    rw [h1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun σ' _ => ?_)
    ring
  have h4 : ∫ z, N z * ‖tp B c z‖ ^ 2 ≤ (∑ σ ∈ B, ∑ σ' ∈ B,
      ((∫ z, (N z : ℂ) * ee z (σ - σ')) + A (σ - σ')) * c σ * starRingEnd ℂ (c σ')).re := by
    rw [h3, Complex.add_re, Complex.ofReal_re]
    linarith
  refine h4.trans ((Complex.re_le_norm _).trans ?_)
  refine le_trans ?_ (schur (fun σ => norm_nonneg _) hsum B (fun σ => ‖c σ‖))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun σ _ => ?_))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun σ' _ => ?_))
  rw [norm_mul, norm_mul, RCLike.norm_conj]

def cube (d : ℕ) : Set (Fin d → ℝ) := Set.Icc (fun _ => -(1 / 2)) (fun _ => 1 / 2)

/- English proof (translation)
Rewrite using `[integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]`. Distinguish the cases in `hm : m = 0`. Simplify using `[hm]`. Evaluate the numerical expressions. Rewrite using `[if_neg hm]`.

Establish `hc : (2 * π * Complex.I * ((m : ℝ) : ℂ)) ≠ 0`. Establish `hpi : (π : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Simplify using `[hm, hpi]`. Repeatedly rewrite using `[← mul_assoc]`. Rewrite using `[integral_exp_mul_complex hc]`.

Establish `: Complex.exp (2 * π * Complex.I * ((m : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ)) = Complex.exp (2 * π * Complex.I * ((m : ℝ) : ℂ) * ((-(1 / 2) : ℝ) : ℂ))`. Rewrite using `[Complex.exp_eq_exp_iff_exists_int]`. Use `⟨m, ?_⟩` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, sub_self, zero_div]`.
-/
lemma integral_one_dim (m : ℤ) :
    ∫ t in Set.Icc (-(1 / 2) : ℝ) (1 / 2), Complex.exp (2 * π * Complex.I * (((m : ℝ) : ℂ) * (t : ℂ))) =
      if m = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  by_cases hm : m = 0
  · simp [hm]; norm_num
  · rw [if_neg hm]
    have hc : (2 * π * Complex.I * ((m : ℝ) : ℂ)) ≠ 0 := by
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hm, hpi]
    simp_rw [← mul_assoc]
    rw [integral_exp_mul_complex hc]
    have : Complex.exp (2 * π * Complex.I * ((m : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ)) =
        Complex.exp (2 * π * Complex.I * ((m : ℝ) : ℂ) * ((-(1 / 2) : ℝ) : ℂ)) := by
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨m, ?_⟩
      push_cast
      ring
    rw [this, sub_self, zero_div]

/- English proof (translation)
Unfold `ee`. Rewrite using `[Finset.mul_sum, Complex.exp_sum]`.
-/
lemma ee_eq_prod (z : Fin d → ℝ) (τ : Fin d → ℤ) :
    ee z τ = ∏ j, Complex.exp (2 * π * Complex.I * (((τ j : ℝ) : ℂ) * (z j : ℂ))) := by
  unfold ee
  rw [Finset.mul_sum, Complex.exp_sum]

/- English proof (translation)
Establish `h1 : ∀ z : Fin d → ℝ, (((cube d).indicator (fun _ => (1 : ℝ)) z : ℝ) : ℂ) * ee z τ = ∏ j, (Set.Icc (-(1 / 2) : ℝ) (1 / 2)).indicator (fun t : ℝ => Complex.exp (2 * π * Complex.I * (((τ j : ℝ) : ℂ) * (t : ℂ)))) (z j)`. Introduce `z`. Distinguish the cases in `hz : z ∈ cube d`. Rewrite using `[Set.indicator_of_mem hz, Complex.ofReal_one, one_mul, ee_eq_prod]`. Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations.

Rewrite using `[Set.indicator_of_mem]`. Conclude with `⟨hz.1 j, hz.2 j⟩`. Rewrite using `[Set.indicator_of_notMem hz, Complex.ofReal_zero, zero_mul]`. Establish `: ∃ j, z j ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2)`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Conclude with `hz ⟨fun j => (hcon j).1, fun j => (hcon j).2⟩`. Take `⟨j, hj⟩` from `this`. Conclude with `(Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)).symm`. Repeatedly rewrite using `[h1]`.

Rewrite using `[integral_fintype_prod_volume_eq_prod]`. Repeatedly rewrite using `[integral_indicator measurableSet_Icc, integral_one_dim]`. Rewrite using `[Finset.prod_ite_zero]`. Simplify using `[funext_iff]`.
-/
lemma integral_cube_ee (τ : Fin d → ℤ) :
    ∫ z, (((cube d).indicator (fun _ => (1 : ℝ)) z : ℝ) : ℂ) * ee z τ = if τ = 0 then 1 else 0 := by
  have h1 : ∀ z : Fin d → ℝ, (((cube d).indicator (fun _ => (1 : ℝ)) z : ℝ) : ℂ) * ee z τ =
      ∏ j, (Set.Icc (-(1 / 2) : ℝ) (1 / 2)).indicator
        (fun t : ℝ => Complex.exp (2 * π * Complex.I * (((τ j : ℝ) : ℂ) * (t : ℂ)))) (z j) := by
    intro z
    by_cases hz : z ∈ cube d
    · rw [Set.indicator_of_mem hz, Complex.ofReal_one, one_mul, ee_eq_prod]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [Set.indicator_of_mem]
      exact ⟨hz.1 j, hz.2 j⟩
    · rw [Set.indicator_of_notMem hz, Complex.ofReal_zero, zero_mul]
      have : ∃ j, z j ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := by
        by_contra hcon
        push Not at hcon
        exact hz ⟨fun j => (hcon j).1, fun j => (hcon j).2⟩
      obtain ⟨j, hj⟩ := this
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)).symm
  simp_rw [h1]
  rw [integral_fintype_prod_volume_eq_prod]
  simp_rw [integral_indicator measurableSet_Icc, integral_one_dim]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

/- English proof (translation)
The claim follows from `isCompact_Icc`.
-/
lemma isCompact_cube : IsCompact (cube d) := isCompact_Icc

/- English proof (translation)
The claim follows from `measurableSet_Icc`.
-/
lemma measurableSet_cube : MeasurableSet (cube d) := measurableSet_Icc

/- English proof (translation)
Rewrite using `[integrable_indicator_iff measurableSet_cube]`. Conclude with `integrableOn_const (isCompact_cube.measure_lt_top.ne)`.
-/
lemma integrable_indicator_cube : Integrable ((cube d).indicator (fun _ => (1 : ℝ))) := by
  rw [integrable_indicator_iff measurableSet_cube]
  exact integrableOn_const (isCompact_cube.measure_lt_top.ne)

/- English proof (translation)
Establish `h` using `integral_mul_normSq_tp (integrable_indicator_cube (d := d)) B c`. Rewrite `h` using `[integral_cube_ee, sub_eq_zero]`. Establish `h2 : (∫ z, (cube d).indicator (fun _ => (1 : ℝ)) z * ‖tp B c z‖ ^ 2) = ∫ z in cube d, ‖tp B c z‖ ^ 2`. Rewrite using `[← integral_indicator measurableSet_cube]`. Use `congr 1`.

Use function extensionality and compare the values at `z`. Distinguish the cases in `hz : z ∈ cube d`. Rewrite using `[Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]`. Rewrite using `[Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]`. Rewrite `h` using `[h2]`.

Establish `h3 : (∑ σ ∈ B, ∑ σ' ∈ B, (if σ = σ' then (1 : ℂ) else 0) * c σ * starRingEnd ℂ (c σ')) = ((∑ σ ∈ B, ‖c σ‖ ^ 2 : ℝ) : ℂ)`. Use `push_cast`. Use `Finset.sum_congr rfl (fun σ hσ => ?_)` and prove the remaining obligations. Repeatedly rewrite using `[ite_mul, zero_mul, one_mul]`. Rewrite using `[Finset.sum_ite_eq, if_pos hσ, Complex.mul_conj']`.

Rewrite `h` using `[h3]`. Conclude with `h` after adjusting the coercions.
-/
lemma parseval (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    ∫ z in cube d, ‖tp B c z‖ ^ 2 = ∑ σ ∈ B, ‖c σ‖ ^ 2 := by
  have h := integral_mul_normSq_tp (integrable_indicator_cube (d := d)) B c
  simp_rw [integral_cube_ee, sub_eq_zero] at h
  have h2 : (∫ z, (cube d).indicator (fun _ => (1 : ℝ)) z * ‖tp B c z‖ ^ 2) =
      ∫ z in cube d, ‖tp B c z‖ ^ 2 := by
    rw [← integral_indicator measurableSet_cube]
    congr 1
    funext z
    by_cases hz : z ∈ cube d
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]
  rw [h2] at h
  have h3 : (∑ σ ∈ B, ∑ σ' ∈ B, (if σ = σ' then (1 : ℂ) else 0) * c σ * starRingEnd ℂ (c σ')) =
      ((∑ σ ∈ B, ‖c σ‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun σ hσ => ?_)
    simp_rw [ite_mul, zero_mul, one_mul]
    rw [Finset.sum_ite_eq, if_pos hσ, Complex.mul_conj']
  rw [h3] at h
  exact_mod_cast h

/- English proof (translation)
Establish `hinj : Function.Injective (fun (p : Fin d → ℕ) (j : Fin d) => (p j : ℤ))`. Introduce `p q h`. Use function extensionality and compare the values at `j`. Use `congrFun h j` as an intermediate fact. Simplify using `using this`.

Use `⟨(Fintype.piFinset fun _ : Fin d => Finset.range (n + 1)).map ⟨_, hinj⟩, fun σ => ∏ j, (n.choose (σ j).toNat : ℂ), fun y => ?_⟩` and prove the remaining obligations. Unfold `tp`. Rewrite using `[Finset.sum_map]`. Repeatedly rewrite using `[add_comm (1 : ℂ), add_pow, one_pow, mul_one]`. Rewrite using `[Finset.prod_univ_sum]`.

Use `Finset.sum_congr rfl (fun p _ => ?_)` and prove the remaining obligations. Rewrite using `[ee_eq_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Simplify using `only [Function.Embedding.coeFn_mk, Int.toNat_natCast]`. Rewrite using `[mul_comm, ← Complex.exp_nat_mul]`.

Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma exists_tp (n : ℕ) : ∃ (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ), ∀ y : Fin d → ℝ,
    tp B c y = ∏ j, (1 + Complex.exp (2 * π * Complex.I * (y j : ℂ))) ^ n := by
  have hinj : Function.Injective (fun (p : Fin d → ℕ) (j : Fin d) => (p j : ℤ)) := by
    intro p q h
    funext j
    have := congrFun h j
    simpa using this
  refine ⟨(Fintype.piFinset fun _ : Fin d => Finset.range (n + 1)).map ⟨_, hinj⟩,
    fun σ => ∏ j, (n.choose (σ j).toNat : ℂ), fun y => ?_⟩
  unfold tp
  rw [Finset.sum_map]
  simp_rw [add_comm (1 : ℂ), add_pow, one_pow, mul_one]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [ee_eq_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp only [Function.Embedding.coeFn_mk, Int.toNat_natCast]
  rw [mul_comm, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/- English proof (translation)
Unfold `tp`. Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Use `congr 1`. Unfold `ee`.

Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Rewrite using `[← mul_add, ← Finset.sum_add_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations.

Simplify using `only [Pi.sub_apply, Pi.neg_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma tp_sub (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) (z z₀ : Fin d → ℝ) :
    tp B c (z - z₀) = tp B (fun σ => c σ * ee (-z₀) σ) z := by
  unfold tp
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [mul_assoc]
  congr 1
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.sub_apply, Pi.neg_apply]
  push_cast
  ring

noncomputable def pk (y : Fin d → ℝ) : ℝ := ∏ j, ‖1 + Complex.exp (2 * π * Complex.I * (y j : ℂ))‖ ^ 2

/- English proof (translation)
Establish `h : (2 * π * Complex.I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`. Rewrite using `[h, Complex.exp_mul_I, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ← Complex.ofReal_cos, ← Complex.ofReal_sin]`. Simplify using `only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.one_im, Complex.mul_im]`. Use polynomial arithmetic with `[Real.sin_sq_add_cos_sq (2 * π * t)]`.
-/
lemma fac_eq (t : ℝ) : ‖1 + Complex.exp (2 * π * Complex.I * (t : ℂ))‖ ^ 2 = 2 + 2 * Real.cos (2 * π * t) := by
  have h : (2 * π * Complex.I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_mul_I, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.one_im, Complex.mul_im]
  nlinarith [Real.sin_sq_add_cos_sq (2 * π * t)]

/- English proof (translation)
Unfold `pk`. Use `fun_prop`.
-/
lemma continuous_pk : Continuous (pk (d := d)) := by
  unfold pk; fun_prop

/- English proof (translation)
The claim follows from `Finset.prod_nonneg (fun j _ => by positivity)`.
-/
lemma pk_nonneg (y : Fin d → ℝ) : 0 ≤ pk y := Finset.prod_nonneg (fun j _ => by positivity)

/- English proof (translation)
Unfold `pk`. Repeatedly rewrite using `[fac_eq]`. Simplify using the standard rewrite rules. Evaluate the numerical expressions.
-/
lemma pk_zero : pk (0 : Fin d → ℝ) = 4 ^ d := by
  unfold pk
  simp_rw [fac_eq]
  simp
  norm_num

/- English proof (translation)
Rewrite using `[pk_zero]`. Distinguish the cases in `hz : ∃ j, ‖1 + Complex.exp (2 * π * Complex.I * (y j : ℂ))‖ ^ 2 = 0`. Take `⟨j, hj⟩` from `hz`. Unfold `pk`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ j) hj]`.

Check the signs of the components of the expression. Use `push Not at hz`. Establish `h4 : (4 : ℝ) ^ d = ∏ _j : Fin d, (4 : ℝ)` using `by simp`. Rewrite using `[h4]`. Unfold `pk`.

Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, y j ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hy0 (funext hcon)`. Use `Finset.prod_lt_prod (fun i _ => lt_of_le_of_ne (by positivity) (hz i).symm) (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩` and prove the remaining obligations.

Rewrite using `[fac_eq]`. Combine the linear relations using `[Real.cos_le_one (2 * π * y i)]`. Rewrite using `[fac_eq]`. Establish `h1` using `hy.1 j`. Establish `h2` using `hy.2 j`.

Establish `hne : Real.cos (2 * π * y j) ≠ 1`. Introduce `h`. Rewrite `h` using `[Real.cos_eq_one_iff_of_lt_of_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]`. Establish `: (2 * π) ≠ 0` using `by positivity`. Conclude with `hj ((mul_eq_zero.1 h).resolve_left this)`.

Use `lt_of_le_of_ne (Real.cos_le_one (2 * π * y j)) hne` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma pk_lt (y : Fin d → ℝ) (hy : y ∈ cube d) (hy0 : y ≠ 0) : pk y < pk (0 : Fin d → ℝ) := by
  rw [pk_zero]
  by_cases hz : ∃ j, ‖1 + Complex.exp (2 * π * Complex.I * (y j : ℂ))‖ ^ 2 = 0
  · obtain ⟨j, hj⟩ := hz
    unfold pk
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hj]
    positivity
  · push Not at hz
    have h4 : (4 : ℝ) ^ d = ∏ _j : Fin d, (4 : ℝ) := by simp
    rw [h4]
    unfold pk
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hy0 (funext hcon)
    refine Finset.prod_lt_prod (fun i _ => lt_of_le_of_ne (by positivity) (hz i).symm)
      (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
    · rw [fac_eq]; linarith [Real.cos_le_one (2 * π * y i)]
    · rw [fac_eq]
      have h1 := hy.1 j
      have h2 := hy.2 j
      have hne : Real.cos (2 * π * y j) ≠ 1 := by
        intro h
        rw [Real.cos_eq_one_iff_of_lt_of_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])] at h
        have : (2 * π) ≠ 0 := by positivity
        exact hj ((mul_eq_zero.1 h).resolve_left this)
      have := lt_of_le_of_ne (Real.cos_le_one (2 * π * y j)) hne
      linarith

/- English proof (translation)
Unfold `pk`. Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[fac_eq, fac_eq, mul_add]`. Use `congr 2`. Use `Real.cos_add_int_mul_two_pi (2 * π * y j) (m j)` as an intermediate fact.

Rewrite using `[← this]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma pk_periodic (y : Fin d → ℝ) (m : Fin d → ℤ) : pk (fun j => y j + (m j : ℝ)) = pk y := by
  unfold pk
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [fac_eq, fac_eq, mul_add]
  congr 2
  have := Real.cos_add_int_mul_two_pi (2 * π * y j) (m j)
  rw [← this]; congr 1; ring

/- English proof (translation)
Establish `h4 : (4 : ℝ) ^ d = ∏ _j : Fin d, (4 : ℝ)` using `by simp`. Rewrite using `[h4]`. Unfold `pk`. Use `Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[fac_eq]`.

Combine the linear relations using `[Real.cos_le_one (2 * π * y i)]`.
-/
lemma pk_le (y : Fin d → ℝ) : pk y ≤ 4 ^ d := by
  have h4 : (4 : ℝ) ^ d = ∏ _j : Fin d, (4 : ℝ) := by simp
  rw [h4]
  unfold pk
  refine Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)
  rw [fac_eq]; linarith [Real.cos_le_one (2 * π * y i)]

/- English proof (translation)
Unfold `pk`. Rewrite using `[norm_prod, ← Finset.prod_pow, ← Finset.prod_pow]`. Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]`.
-/
lemma normSq_prod (n : ℕ) (y : Fin d → ℝ) :
    ‖∏ j, (1 + Complex.exp (2 * π * Complex.I * (y j : ℂ))) ^ n‖ ^ 2 = pk y ^ n := by
  unfold pk
  rw [norm_prod, ← Finset.prod_pow, ← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [norm_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]

/- English proof (translation)
Take `⟨B, c, hBc⟩` from `exists_tp (d := d) n`. Establish `hpk : ∀ y, ‖tp B c y‖ ^ 2 = pk y ^ n` using `fun y => by rw [hBc, normSq_prod]`. Establish `h1` using `key_upper hint hPD hsum B (fun σ => c σ * ee (-z₀) σ)`. Rewrite `h1` using `[← tp_sub, hpk, norm_mul, norm_ee, mul_one]`. Rewrite `h1` using `[← parseval]`.

Rewrite `h1` using `[hpk]`. Conclude with `h1`.
-/
lemma upper_pk {N : (Fin d → ℝ) → ℝ} {A : (Fin d → ℤ) → ℂ} (hint : Integrable N)
    (hPD : ∀ (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
        0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * starRingEnd ℂ (c σ')).re)
    (hsum : Summable (fun σ : Fin d → ℤ => ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖))
    (z₀ : Fin d → ℝ) (n : ℕ) :
    ∫ z, N z * pk (z - z₀) ^ n ≤
      (∑' σ : Fin d → ℤ, ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖) * ∫ y in cube d, pk y ^ n := by
  obtain ⟨B, c, hBc⟩ := exists_tp (d := d) n
  have hpk : ∀ y, ‖tp B c y‖ ^ 2 = pk y ^ n := fun y => by rw [hBc, normSq_prod]
  have h1 := key_upper hint hPD hsum B (fun σ => c σ * ee (-z₀) σ)
  simp_rw [← tp_sub, hpk, norm_mul, norm_ee, mul_one] at h1
  rw [← parseval] at h1
  simp_rw [hpk] at h1
  exact h1

/- English proof (translation)
Use `hint.mul_bdd (c := (4 ^ d) ^ n) ?_ (Eventually.of_forall (fun z => ?_))` and prove the remaining obligations. Conclude with `((continuous_pk.comp (continuous_id.sub continuous_const)).pow n).aestronglyMeasurable`. Rewrite using `[Real.norm_of_nonneg (pow_nonneg (pk_nonneg _) n)]`. Conclude with `pow_le_pow_left₀ (pk_nonneg _) (pk_le _) n`.
-/
lemma integrable_mul_pk {N : (Fin d → ℝ) → ℝ} (hint : Integrable N) (z₀ : Fin d → ℝ) (n : ℕ) :
    Integrable (fun z => N z * pk (z - z₀) ^ n) := by
  refine hint.mul_bdd (c := (4 ^ d) ^ n) ?_ (Eventually.of_forall (fun z => ?_))
  · exact ((continuous_pk.comp (continuous_id.sub continuous_const)).pow n).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (pow_nonneg (pk_nonneg _) n)]
    exact pow_le_pow_left₀ (pk_nonneg _) (pk_le _) n

/- English proof (translation)
Use `set G : (Fin d → ℝ) → ℝ := fun y => pk y ^ n • U.indicator (fun _ => (1 : ℝ)) y with hG`. Establish `hUc : U ⊆ cube d` using `fun y hy => ⟨fun j => (abs_lt.1 (hU2 y hy j)).1.le, fun j => (abs_lt.1 (hU2 y hy j)).2.le⟩`. Establish `hGint0 : IntegrableOn G (cube d)`. Establish `h1 : IntegrableOn (fun y : Fin d → ℝ => pk y ^ n) (cube d)` using `(continuous_pk.pow n).continuousOn.integrableOn_compact isCompact_cube`. Establish `h2` using `h1.indicator hUo.measurableSet`.

Use `h2.congr (Eventually.of_forall (fun y => ?_))` and prove the remaining obligations. Distinguish the cases in `hy : y ∈ U`. Simplify using `[hG, hy]`. Simplify using `[hG, hy]`. Establish `hGz : ∀ y, y ∉ cube d → G y = 0`.

Introduce `y hy`. Establish `: y ∉ U` using `fun h => hy (hUc h)`. Simplify using `[hG, this]`. Establish `hGint : Integrable G`. Rewrite using `[← integrableOn_univ]`.

Use `(integrableOn_iff_integrable_of_support_subset ?_).1 hGint0 |>.integrableOn` and prove the remaining obligations. Introduce `y hy`. Assume the negation of the conclusion as `hc`. Conclude with `hy (hGz y hc)`. Rewrite using `[setIntegral_eq_integral_of_forall_compl_eq_zero hGz]`.

Establish `hpt : ∀ z, ∑ m ∈ S, (N (fun j => z₀ j + (m j : ℝ)) - η) * G (z - fun j => z₀ j + (m j : ℝ)) ≤ N z * pk (z - z₀) ^ n`. Introduce `z`. Establish `hR : 0 ≤ N z * pk (z - z₀) ^ n` using `mul_nonneg (hN0 z) (pow_nonneg (pk_nonneg _) n)`. Distinguish the cases in `h : ∃ m ∈ S, (z - fun j => z₀ j + (m j : ℝ)) ∈ U`. Take `⟨m, hm, hmU⟩` from `h`.

Rewrite using `[Finset.sum_eq_single_of_mem m hm]`. Establish `hper : pk (z - fun j => z₀ j + (m j : ℝ)) = pk (z - z₀)`. Rewrite using `[← pk_periodic (z - fun j => z₀ j + (m j : ℝ)) m]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Simplify using `only [Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hz : (fun j => z₀ j + (m j : ℝ) + (z - fun j => z₀ j + (m j : ℝ)) j) = z`. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.sub_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `hU1 _ hmU m hm`. Rewrite `h1` using `[hz]`. Simplify using `only [hG, Set.indicator_of_mem hmU, smul_eq_mul, mul_one, hper]`. Conclude with `mul_le_mul_of_nonneg_right h1.le (pow_nonneg (pk_nonneg _) n)`.

Introduce `m' hm' hne`. Establish `: (z - fun j => z₀ j + (m' j : ℝ)) ∉ U`. Introduce `hm'U`. Apply `hne` to reduce the goal to its premises. Use function extensionality and compare the values at `j`.

Establish `a1` using `abs_lt.1 (hU2 _ hmU j)`. Establish `a2` using `abs_lt.1 (hU2 _ hm'U j)`. Simplify using `only [Pi.sub_apply] at a1 a2`. Establish `b1 : ((m' j - m j : ℤ) : ℝ) < 1` using `by push_cast; linarith [a1.1, a1.2, a2.1, a2.2]`. Establish `b2 : (-1 : ℝ) < ((m' j - m j : ℤ) : ℝ)` using `by push_cast; linarith [a1.1, a1.2, a2.1, a2.2]`.

Establish `c1 : m' j - m j < 1` using `by exact_mod_cast b1`. Establish `c2 : -1 < m' j - m j` using `by exact_mod_cast b2`. Use linear arithmetic over natural numbers and integers. Simplify using `[hG, this]`. Use `push Not at h`.

Rewrite using `[Finset.sum_eq_zero]`. Conclude with `hR`. Introduce `m hm`. Simplify using `[hG, h m hm]`. Establish `hmono` using `integral_mono (integrable_finsetSum S (fun m _ => (hGint.comp_sub_right (fun j => z₀ j + (m j : ℝ))).const_mul (N (fun j => z₀ j + (m j : ℝ)) - η))) (integrable_mul_pk hint z₀ n) hpt`.

Rewrite `hmono` using `[integral_finsetSum]`. Rewrite `hmono` using `[integral_const_mul, integral_sub_right_eq_self G]`. Rewrite `hmono` using `[← Finset.sum_mul]`. Conclude with `hmono`. Introduce `m _`.

Conclude with `(hGint.comp_sub_right (fun j => z₀ j + (m j : ℝ))).const_mul _`.
-/
lemma lower_pk {N : (Fin d → ℝ) → ℝ} (hN0 : ∀ z, 0 ≤ N z) (hint : Integrable N)
    (z₀ : Fin d → ℝ) (S : Finset (Fin d → ℤ)) (η : ℝ) (U : Set (Fin d → ℝ)) (hUo : IsOpen U)
    (hU1 : ∀ y ∈ U, ∀ m ∈ S, N (fun j => z₀ j + (m j : ℝ)) - η < N (fun j => z₀ j + (m j : ℝ) + y j))
    (hU2 : ∀ y ∈ U, ∀ j, |y j| < 1 / 2) (n : ℕ) :
    (∑ m ∈ S, (N (fun j => z₀ j + (m j : ℝ)) - η)) *
      (∫ y in cube d, pk y ^ n • U.indicator (fun _ => (1 : ℝ)) y) ≤ ∫ z, N z * pk (z - z₀) ^ n := by
  set G : (Fin d → ℝ) → ℝ := fun y => pk y ^ n • U.indicator (fun _ => (1 : ℝ)) y with hG
  have hUc : U ⊆ cube d := fun y hy =>
    ⟨fun j => (abs_lt.1 (hU2 y hy j)).1.le, fun j => (abs_lt.1 (hU2 y hy j)).2.le⟩
  have hGint0 : IntegrableOn G (cube d) := by
    have h1 : IntegrableOn (fun y : Fin d → ℝ => pk y ^ n) (cube d) :=
      (continuous_pk.pow n).continuousOn.integrableOn_compact isCompact_cube
    have h2 := h1.indicator hUo.measurableSet
    refine h2.congr (Eventually.of_forall (fun y => ?_))
    by_cases hy : y ∈ U
    · simp [hG, hy]
    · simp [hG, hy]
  have hGz : ∀ y, y ∉ cube d → G y = 0 := by
    intro y hy
    have : y ∉ U := fun h => hy (hUc h)
    simp [hG, this]
  have hGint : Integrable G := by
    rw [← integrableOn_univ]
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 hGint0 |>.integrableOn
    intro y hy
    by_contra hc
    exact hy (hGz y hc)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hGz]
  have hpt : ∀ z, ∑ m ∈ S, (N (fun j => z₀ j + (m j : ℝ)) - η) * G (z - fun j => z₀ j + (m j : ℝ)) ≤
      N z * pk (z - z₀) ^ n := by
    intro z
    have hR : 0 ≤ N z * pk (z - z₀) ^ n := mul_nonneg (hN0 z) (pow_nonneg (pk_nonneg _) n)
    by_cases h : ∃ m ∈ S, (z - fun j => z₀ j + (m j : ℝ)) ∈ U
    · obtain ⟨m, hm, hmU⟩ := h
      rw [Finset.sum_eq_single_of_mem m hm]
      · have hper : pk (z - fun j => z₀ j + (m j : ℝ)) = pk (z - z₀) := by
          rw [← pk_periodic (z - fun j => z₀ j + (m j : ℝ)) m]
          congr 1
          funext j
          simp only [Pi.sub_apply]
          ring
        have hz : (fun j => z₀ j + (m j : ℝ) + (z - fun j => z₀ j + (m j : ℝ)) j) = z := by
          funext j
          simp only [Pi.sub_apply]
          ring
        have h1 := hU1 _ hmU m hm
        rw [hz] at h1
        simp only [hG, Set.indicator_of_mem hmU, smul_eq_mul, mul_one, hper]
        exact mul_le_mul_of_nonneg_right h1.le (pow_nonneg (pk_nonneg _) n)
      · intro m' hm' hne
        have : (z - fun j => z₀ j + (m' j : ℝ)) ∉ U := by
          intro hm'U
          apply hne
          funext j
          have a1 := abs_lt.1 (hU2 _ hmU j)
          have a2 := abs_lt.1 (hU2 _ hm'U j)
          simp only [Pi.sub_apply] at a1 a2
          have b1 : ((m' j - m j : ℤ) : ℝ) < 1 := by push_cast; linarith [a1.1, a1.2, a2.1, a2.2]
          have b2 : (-1 : ℝ) < ((m' j - m j : ℤ) : ℝ) := by push_cast; linarith [a1.1, a1.2, a2.1, a2.2]
          have c1 : m' j - m j < 1 := by exact_mod_cast b1
          have c2 : -1 < m' j - m j := by exact_mod_cast b2
          omega
        simp [hG, this]
    · push Not at h
      rw [Finset.sum_eq_zero]
      · exact hR
      · intro m hm
        simp [hG, h m hm]
  have hmono := integral_mono
    (integrable_finsetSum S (fun m _ =>
      (hGint.comp_sub_right (fun j => z₀ j + (m j : ℝ))).const_mul
        (N (fun j => z₀ j + (m j : ℝ)) - η)))
    (integrable_mul_pk hint z₀ n) hpt
  rw [integral_finsetSum] at hmono
  · simp_rw [integral_const_mul, integral_sub_right_eq_self G] at hmono
    rw [← Finset.sum_mul] at hmono
    exact hmono
  · intro m _
    exact (hGint.comp_sub_right (fun j => z₀ j + (m j : ℝ))).const_mul _

end Formalism.FourierDecayAlt.P.HLsc

namespace Formalism.FourierDecayAlt.P

open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz Formalism.FourierDecayAlt.P.HLsc

/- English proof (translation)
Introduce `d N A hN0 hlsc hint hPD hsum z₀ S`. Express the relevant statement in the definitionally equal form `Summable (fun σ : Fin d → ℤ => ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖) at hsum`. Express the relevant statement in the definitionally equal form `_ ≤ ∑' σ : Fin d → ℤ, ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖`. Use `set K := ∑' σ : Fin d → ℤ, ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖ with hK`. Establish `hK0 : 0 ≤ K` using `tsum_nonneg (fun _ => norm_nonneg _)`.

Use `le_of_forall_pos_le_add (fun ε hε => ?_)` and prove the remaining obligations. Use `set η : ℝ := ε / ((S.card : ℝ) + 1) with hη`. Establish `hηpos : 0 < η` using `by positivity`. Establish `hev : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), ∀ m ∈ S, N (fun j => z₀ j + (m j : ℝ)) - η < N (fun j => z₀ j + (m j : ℝ) + y j)`. Rewrite using `[Filter.eventually_all_finset]`.

Introduce `m _`. Establish `h1` using `hlsc (fun j => z₀ j + (m j : ℝ)) (N (fun j => z₀ j + (m j : ℝ)) - η) (by linarith)`. Establish `h2 : Tendsto (fun y : Fin d → ℝ => (fun j => z₀ j + (m j : ℝ) + y j)) (𝓝 0) (𝓝 (fun j => z₀ j + (m j : ℝ)))`. Establish `hc : Continuous (fun y : Fin d → ℝ => (fun j => z₀ j + (m j : ℝ) + y j))` using `by fun_prop`. Conclude with `hc.tendsto' _ _ (by simp)`.

Conclude with `h2.eventually h1`. Establish `hball : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), ∀ j, |y j| < 1 / 2` using `by filter_upwards [Metric.ball_mem_nhds (0 : Fin d → ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with y hy j`. Rewrite `hy` using `[mem_ball_zero_iff]`. Conclude with `lt_of_le_of_lt (norm_le_pi_norm y j) hy`. Take `⟨U, hUsub, hUo, h0U⟩` from `mem_nhds_iff.1 (hev.and hball)`.

Establish `hT` using `tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn (μ := (volume : Measure (Fin d → ℝ))) (x₀ := 0) (g := U.indicator (fun _ => (1 : ℝ))) isCompact_cube continuous_pk.continuousOn pk_lt (fun x _ => pk_nonneg x) (by rw [pk_zero]; positivity) (subset_closure …`. Establish `: U.indicator (fun _ => (1 : ℝ)) =ᶠ[𝓝 0] fun _ => (1 : ℝ)` using `by filter_upwards [hUo.mem_nhds h0U] with y hy`. Conclude with `Set.indicator_of_mem hy _`. Conclude with `(continuousAt_const.congr this.symm).continuousWithinAt)`. Rewrite `hT` using `[Set.indicator_of_mem h0U]`.

Establish `hle : ∀ n : ℕ, (∑ m ∈ S, (N (fun j => z₀ j + (m j : ℝ)) - η)) * ((∫ x in cube d, pk x ^ n)⁻¹ • ∫ x in cube d, pk x ^ n • U.indicator (fun _ => (1 : ℝ)) x) ≤ K`. Introduce `n`. Establish `h1` using `(lower_pk hN0 hint z₀ S η U hUo (fun y hy => (hUsub hy).1) (fun y hy => (hUsub hy).2) n).trans (upper_pk hint hPD hsum z₀ n)`. Establish `hI : 0 ≤ ∫ x in cube d, pk x ^ n` using `integral_nonneg (fun x => pow_nonneg (pk_nonneg x) n)`. Establish `h2` using `mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hI)`.

Establish `h3 : K * (∫ x in cube d, pk x ^ n) * (∫ x in cube d, pk x ^ n)⁻¹ ≤ K`. Rewrite using `[mul_assoc]`. Conclude with `mul_le_of_le_one_right hK0 mul_inv_le_one`. Rewrite using `[smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hlim` using `le_of_tendsto' (hT.const_mul (∑ m ∈ S, (N (fun j => z₀ j + (m j : ℝ)) - η))) hle`. Rewrite `hlim` using `[mul_one, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]`. Establish `hfin : (S.card : ℝ) * η ≤ ε`. Rewrite using `[hη, mul_div_assoc', div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem herglotz_lower_semicontinuous : Formalism.FourierDecayAlt.E.HerglotzLSC := by
  intro d N A hN0 hlsc hint hPD hsum z₀ S
  change Summable (fun σ : Fin d → ℤ => ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖) at hsum
  change _ ≤ ∑' σ : Fin d → ℤ, ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖
  set K := ∑' σ : Fin d → ℤ, ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖ with hK
  have hK0 : 0 ≤ K := tsum_nonneg (fun _ => norm_nonneg _)
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  set η : ℝ := ε / ((S.card : ℝ) + 1) with hη
  have hηpos : 0 < η := by positivity
  have hev : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), ∀ m ∈ S,
      N (fun j => z₀ j + (m j : ℝ)) - η < N (fun j => z₀ j + (m j : ℝ) + y j) := by
    rw [Filter.eventually_all_finset]
    intro m _
    have h1 := hlsc (fun j => z₀ j + (m j : ℝ)) (N (fun j => z₀ j + (m j : ℝ)) - η) (by linarith)
    have h2 : Tendsto (fun y : Fin d → ℝ => (fun j => z₀ j + (m j : ℝ) + y j)) (𝓝 0)
        (𝓝 (fun j => z₀ j + (m j : ℝ))) := by
      have hc : Continuous (fun y : Fin d → ℝ => (fun j => z₀ j + (m j : ℝ) + y j)) := by fun_prop
      exact hc.tendsto' _ _ (by simp)
    exact h2.eventually h1
  have hball : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), ∀ j, |y j| < 1 / 2 := by
    filter_upwards [Metric.ball_mem_nhds (0 : Fin d → ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with y hy j
    rw [mem_ball_zero_iff] at hy
    exact lt_of_le_of_lt (norm_le_pi_norm y j) hy
  obtain ⟨U, hUsub, hUo, h0U⟩ := mem_nhds_iff.1 (hev.and hball)
  have hT := tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn
    (μ := (volume : Measure (Fin d → ℝ))) (x₀ := 0) (g := U.indicator (fun _ => (1 : ℝ)))
    isCompact_cube continuous_pk.continuousOn pk_lt (fun x _ => pk_nonneg x)
    (by rw [pk_zero]; positivity)
    (subset_closure (mem_interior_iff_mem_nhds.2
      (pi_Icc_mem_nhds (fun _ => by norm_num) (fun _ => by norm_num))))
    ((integrableOn_const (isCompact_cube.measure_lt_top.ne)).indicator hUo.measurableSet)
    (by
      have : U.indicator (fun _ => (1 : ℝ)) =ᶠ[𝓝 0] fun _ => (1 : ℝ) := by
        filter_upwards [hUo.mem_nhds h0U] with y hy
        exact Set.indicator_of_mem hy _
      exact (continuousAt_const.congr this.symm).continuousWithinAt)
  rw [Set.indicator_of_mem h0U] at hT
  have hle : ∀ n : ℕ, (∑ m ∈ S, (N (fun j => z₀ j + (m j : ℝ)) - η)) *
      ((∫ x in cube d, pk x ^ n)⁻¹ • ∫ x in cube d, pk x ^ n • U.indicator (fun _ => (1 : ℝ)) x) ≤ K := by
    intro n
    have h1 := (lower_pk hN0 hint z₀ S η U hUo (fun y hy => (hUsub hy).1) (fun y hy => (hUsub hy).2) n).trans
      (upper_pk hint hPD hsum z₀ n)
    have hI : 0 ≤ ∫ x in cube d, pk x ^ n := integral_nonneg (fun x => pow_nonneg (pk_nonneg x) n)
    have h2 := mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hI)
    have h3 : K * (∫ x in cube d, pk x ^ n) * (∫ x in cube d, pk x ^ n)⁻¹ ≤ K := by
      rw [mul_assoc]
      exact mul_le_of_le_one_right hK0 mul_inv_le_one
    rw [smul_eq_mul]
    calc _ = _ := by ring
      _ ≤ _ := h2
      _ ≤ K := h3
  have hlim := le_of_tendsto' (hT.const_mul (∑ m ∈ S, (N (fun j => z₀ j + (m j : ℝ)) - η))) hle
  rw [mul_one, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hlim
  have hfin : (S.card : ℝ) * η ≤ ε := by
    rw [hη, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end Formalism.FourierDecayAlt.P
