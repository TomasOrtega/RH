import Mathlib
import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula

open Finset Filter Topology MeasureTheory

namespace Formalism.HermitianLattices.GL2PrimeSums

section abel

variable {𝕜 : Type*} [RCLike 𝕜]

/- English proof (translation)
Establish `h` using `(RCLike.ofRealCLM (K := 𝕜)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_inv ht)`. Establish `hfun : (fun u : ℝ => ((u : 𝕜))⁻¹) = (RCLike.ofRealCLM (K` using `𝕜)) ∘ fun y : ℝ => y⁻¹ := by`. Use function extensionality and compare the values at `u`. Simplify using the standard rewrite rules. Rewrite using `[hfun]`.

Conclude with `h.congr_deriv (by simp)`.
-/
private lemma hasDerivAt_inv_coe (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ => ((u : 𝕜))⁻¹) (-((t : 𝕜) ^ 2)⁻¹) t := by
  have h := (RCLike.ofRealCLM (K := 𝕜)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_inv ht)
  have hfun : (fun u : ℝ => ((u : 𝕜))⁻¹) = (RCLike.ofRealCLM (K := 𝕜)) ∘ fun y : ℝ => y⁻¹ := by
    funext u
    simp
  rw [hfun]
  exact h.congr_deriv (by simp)

/- English proof (translation)
Use extensionality with `k`. Simplify using `only [Finset.mem_Icc, Finset.mem_Ioc]`. Use linear arithmetic over natural numbers and integers.
-/
private lemma Icc_one_eq_Ioc_zero (N : ℕ) : Icc 1 N = Ioc 0 N := by
  ext k
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/- English proof (translation)
Use `ContinuousOn.inv₀ ((RCLike.continuous_ofReal (K := 𝕜)).pow 2).continuousOn ?_` and prove the remaining obligations. Introduce `t ht`. Establish `: (t : 𝕜) ≠ 0`. Rewrite using `[Ne, RCLike.ofReal_eq_zero]`. Conclude with `(show (0 : ℝ) < t by linarith [ht.1]).ne'`.

Conclude with `pow_ne_zero 2 this`.
-/
private theorem continuousOn_inv_sq_Icc_of_pos {y U : ℝ} (hy : 0 < y) :
    ContinuousOn (fun t : ℝ => ((t : 𝕜) ^ 2)⁻¹) (Set.Icc y U) := by
  refine ContinuousOn.inv₀ ((RCLike.continuous_ofReal (K := 𝕜)).pow 2).continuousOn ?_
  intro t ht
  have : (t : 𝕜) ≠ 0 := by
    rw [Ne, RCLike.ofReal_eq_zero]
    exact (show (0 : ℝ) < t by linarith [ht.1]).ne'
  exact pow_ne_zero 2 this

/- English proof (translation)
Establish `hg : IntegrableOn (fun t : ℝ => ((t : 𝕜) ^ 2)⁻¹) (Set.Icc y U)` using `(continuousOn_inv_sq_Icc_of_pos (by linarith)).integrableOn_Icc`. Use `integrableOn_mul_sum_Icc c (m := 1) (by linarith : (0 : ℝ) ≤ y) hg` as an intermediate fact. Use `this.congr_fun (fun t _ => ?_) measurableSet_Icc` and prove the remaining obligations. Simplify using `only [div_eq_inv_mul]`.
-/
private lemma integrableOn_partial_sum_div_sq (c : ℕ → 𝕜) {y U : ℝ} (hy : 1 ≤ y) :
    IntegrableOn (fun u : ℝ => (∑ n ∈ Icc 1 ⌊u⌋₊, c n) / (u : 𝕜) ^ 2) (Set.Icc y U) := by
  have hg : IntegrableOn (fun t : ℝ => ((t : 𝕜) ^ 2)⁻¹) (Set.Icc y U) :=
    (continuousOn_inv_sq_Icc_of_pos (by linarith)).integrableOn_Icc
  have := integrableOn_mul_sum_Icc c (m := 1) (by linarith : (0 : ℝ) ≤ y) hg
  refine this.congr_fun (fun t _ => ?_) measurableSet_Icc
  simp only [div_eq_inv_mul]

/- English proof (translation)
Rewrite using `[Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons, Icc_one_eq_Ioc_zero]`. Simplify using `only [↓reduceIte, zero_add]`. Conclude with `Finset.sum_congr rfl fun k hk => if_neg (Finset.mem_Ioc.mp hk).1.ne'`.
-/
private theorem sum_Icc_zero_ite_eq_sum_Icc_one (c : ℕ → 𝕜) (N : ℕ) :
    ∑ k ∈ Icc 0 N, (if k = 0 then (0 : 𝕜) else c k) = ∑ k ∈ Icc 1 N, c k := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons, Icc_one_eq_Ioc_zero]
  simp only [↓reduceIte, zero_add]
  exact Finset.sum_congr rfl fun k hk => if_neg (Finset.mem_Ioc.mp hk).1.ne'

/- English proof (translation)
Establish `hy0 : (0 : ℝ) ≤ y` using `by linarith`. Establish `hne : ∀ t ∈ Set.Icc y U, t ≠ 0` using `fun t ht => (show (0 : ℝ) < t by linarith [ht.1]).ne'`. Establish `hf_diff : ∀ t ∈ Set.Icc y U, DifferentiableAt ℝ (fun u : ℝ => ((u : 𝕜))⁻¹) t` using `fun t ht => (hasDerivAt_inv_coe t (hne t ht)).differentiableAt`. Establish `hf_int : IntegrableOn (deriv (fun u : ℝ => ((u : 𝕜))⁻¹)) (Set.Icc y U)`. Use `((continuousOn_inv_sq_Icc_of_pos (𝕜 := 𝕜) (U := U) (by linarith)).neg.integrableOn_Icc).congr_fun (fun t ht => ?_) measurableSet_Icc` and prove the remaining obligations.

Conclude with `((hasDerivAt_inv_coe t (hne t ht)).deriv).symm`. Establish `key : ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, ((k : ℝ) : 𝕜)⁻¹ * (if k = 0 then (0 : 𝕜) else c k) = ((U : 𝕜))⁻¹ * (∑ k ∈ Icc 0 ⌊U⌋₊, (if k = 0 then (0 : 𝕜) else c k)) - ((y : 𝕜))⁻¹ * (∑ k ∈ Icc 0 ⌊y⌋₊, (if k = 0 then (0 : 𝕜) else c k)) - ∫ t in Set.Ioc y U, deriv (fun u : ℝ => ((u : 𝕜))⁻¹) t * ∑ k ∈ …` using `sum_mul_eq_sub_sub_integral_mul (fun n => if n = 0 then (0 : 𝕜) else c n) hy0 hU hf_diff hf_int`. Establish `hL : ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, ((k : ℝ) : 𝕜)⁻¹ * (if k = 0 then (0 : 𝕜) else c k) = (∑ n ∈ Icc 1 ⌊U⌋₊, c n / (n : 𝕜)) - (∑ n ∈ Icc 1 ⌊y⌋₊, c n / (n : 𝕜))`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations.

Establish `hk0 : k ≠ 0` using `(lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hk).1).ne'`. Rewrite using `[if_neg hk0, RCLike.ofReal_natCast]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by`. Rewrite using `[Icc_one_eq_Ioc_zero, Icc_one_eq_Ioc_zero]`.

Conclude with `eq_sub_of_add_eq' (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_le_floor hU))`. Establish `hint_r : ∫ t in Set.Ioc y U, deriv (fun u : ℝ => ((u : 𝕜))⁻¹) t * ∑ k ∈ Icc 0 ⌊t⌋₊, (if k = 0 then (0 : 𝕜) else c k) = -∫ t in Set.Ioc y U, (∑ n ∈ Icc 1 ⌊t⌋₊, c n) / (t : 𝕜) ^ 2`. Rewrite using `[← integral_neg]`. Use `setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_` and prove the remaining obligations. Establish `ht0 : t ≠ 0` using `(show (0 : ℝ) < t by linarith [ht.1]).ne'`.

Simplify using `only [(hasDerivAt_inv_coe (𝕜 := 𝕜) t ht0).deriv, sum_Icc_zero_ite_eq_sum_Icc_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[intervalIntegral.integral_of_le hU]`. Take the linear combination `-key + hL + hint_r - ((U : 𝕜))⁻¹ * sum_Icc_zero_ite_eq_sum_Icc_one c ⌊U⌋₊ + ((y : 𝕜))⁻¹ * sum_Icc_zero_ite_eq_sum_Icc_one c ⌊y⌋₊`.
-/
private lemma integral_partial_sum_div_sq (c : ℕ → 𝕜) {y U : ℝ} (hy : 1 ≤ y) (hU : y ≤ U) :
    ∫ u in y..U, (∑ n ∈ Icc 1 ⌊u⌋₊, c n) / (u : 𝕜) ^ 2 =
      (∑ n ∈ Icc 1 ⌊U⌋₊, c n / (n : 𝕜)) - (∑ n ∈ Icc 1 ⌊y⌋₊, c n / (n : 𝕜))
        - (∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (U : 𝕜) + (∑ n ∈ Icc 1 ⌊y⌋₊, c n) / (y : 𝕜) := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hne : ∀ t ∈ Set.Icc y U, t ≠ 0 := fun t ht => (show (0 : ℝ) < t by linarith [ht.1]).ne'
  have hf_diff : ∀ t ∈ Set.Icc y U, DifferentiableAt ℝ (fun u : ℝ => ((u : 𝕜))⁻¹) t :=
    fun t ht => (hasDerivAt_inv_coe t (hne t ht)).differentiableAt
  have hf_int : IntegrableOn (deriv (fun u : ℝ => ((u : 𝕜))⁻¹)) (Set.Icc y U) := by
    refine ((continuousOn_inv_sq_Icc_of_pos (𝕜 := 𝕜) (U := U) (by linarith)).neg.integrableOn_Icc).congr_fun
      (fun t ht => ?_) measurableSet_Icc
    exact ((hasDerivAt_inv_coe t (hne t ht)).deriv).symm
  have key : ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, ((k : ℝ) : 𝕜)⁻¹ * (if k = 0 then (0 : 𝕜) else c k) =
      ((U : 𝕜))⁻¹ * (∑ k ∈ Icc 0 ⌊U⌋₊, (if k = 0 then (0 : 𝕜) else c k))
        - ((y : 𝕜))⁻¹ * (∑ k ∈ Icc 0 ⌊y⌋₊, (if k = 0 then (0 : 𝕜) else c k))
        - ∫ t in Set.Ioc y U, deriv (fun u : ℝ => ((u : 𝕜))⁻¹) t *
            ∑ k ∈ Icc 0 ⌊t⌋₊, (if k = 0 then (0 : 𝕜) else c k) :=
    sum_mul_eq_sub_sub_integral_mul (fun n => if n = 0 then (0 : 𝕜) else c n) hy0 hU hf_diff hf_int
  have hL : ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, ((k : ℝ) : 𝕜)⁻¹ * (if k = 0 then (0 : 𝕜) else c k) =
      (∑ n ∈ Icc 1 ⌊U⌋₊, c n / (n : 𝕜)) - (∑ n ∈ Icc 1 ⌊y⌋₊, c n / (n : 𝕜)) := by
    calc ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, ((k : ℝ) : 𝕜)⁻¹ * (if k = 0 then (0 : 𝕜) else c k)
        = ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, c k / (k : 𝕜) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk0 : k ≠ 0 := (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hk).1).ne'
          rw [if_neg hk0, RCLike.ofReal_natCast]
          ring
      _ = _ := by
          rw [Icc_one_eq_Ioc_zero, Icc_one_eq_Ioc_zero]
          exact eq_sub_of_add_eq' (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_le_floor hU))
  have hint_r : ∫ t in Set.Ioc y U, deriv (fun u : ℝ => ((u : 𝕜))⁻¹) t *
        ∑ k ∈ Icc 0 ⌊t⌋₊, (if k = 0 then (0 : 𝕜) else c k) =
      -∫ t in Set.Ioc y U, (∑ n ∈ Icc 1 ⌊t⌋₊, c n) / (t : 𝕜) ^ 2 := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht0 : t ≠ 0 := (show (0 : ℝ) < t by linarith [ht.1]).ne'
    simp only [(hasDerivAt_inv_coe (𝕜 := 𝕜) t ht0).deriv, sum_Icc_zero_ite_eq_sum_Icc_one]
    ring
  rw [intervalIntegral.integral_of_le hU]
  linear_combination -key + hL + hint_r - ((U : 𝕜))⁻¹ * sum_Icc_zero_ite_eq_sum_Icc_one c ⌊U⌋₊
    + ((y : 𝕜))⁻¹ * sum_Icc_zero_ite_eq_sum_Icc_one c ⌊y⌋₊

end abel

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ N ih`. Rewrite using `[Finset.sum_Icc_succ_top (Nat.le_add_left 1 N), Finset.sum_Icc_succ_top (Nat.le_add_left 1 N), Finset.sum_range_succ, ih]`. Establish `hN : ((N : ℂ) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero N`.

Establish `e : ((N : ℂ) + 1) * (c (N + 1) / ((N : ℂ) + 1)) = c (N + 1)` using `by field_simp`. Use `push_cast`. Take the linear combination `-e`.
-/
private theorem sum_Icc_eq_mul_sum_div_sub_sum_partial (c : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, c n = (N : ℂ) * (∑ n ∈ Icc 1 N, c n / (n : ℂ))
      - ∑ k ∈ range N, ∑ n ∈ Icc 1 k, c n / (n : ℂ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 N), Finset.sum_Icc_succ_top (Nat.le_add_left 1 N),
      Finset.sum_range_succ, ih]
    have hN : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    have e : ((N : ℂ) + 1) * (c (N + 1) / ((N : ℂ) + 1)) = c (N + 1) := by field_simp
    push_cast
    linear_combination -e

/- English proof (translation)
Establish `hc` using `h.cesaro_smul`. Establish `hd` using `h.sub hc`. Rewrite `hd` using `[sub_self]`. Use `hd.congr' ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop 1] with N hN`.

Rewrite using `[sum_Icc_eq_mul_sum_div_sub_sum_partial c N, Complex.real_smul]`. Establish `hN0 : (N : ℂ) ≠ 0` using `by exact_mod_cast (show N ≠ 0 by omega)`. Establish `e : (N : ℂ) * (∑ n ∈ Icc 1 N, c n / (n : ℂ)) / (N : ℂ) = ∑ n ∈ Icc 1 N, c n / (n : ℂ)`. Clear the denominators using the available nonvanishing facts. Use `push_cast`.

Take the linear combination `-e`.
-/
private lemma kronecker_tendsto_zero (c : ℕ → ℂ) (S : ℂ)
    (h : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, c n / (n : ℂ)) atTop (𝓝 S)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, c n) / (N : ℂ)) atTop (𝓝 0) := by
  have hc := h.cesaro_smul
  have hd := h.sub hc
  rw [sub_self] at hd
  refine hd.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [sum_Icc_eq_mul_sum_div_sub_sum_partial c N, Complex.real_smul]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have e : (N : ℂ) * (∑ n ∈ Icc 1 N, c n / (n : ℂ)) / (N : ℂ) = ∑ n ∈ Icc 1 N, c n / (n : ℂ) := by
    field_simp
  push_cast
  linear_combination -e

/- English proof (translation)
Establish `h0` using `(kronecker_tendsto_zero c S h).comp (tendsto_nat_floor_atTop (α := ℝ))`. Establish `h1 : Tendsto (fun U : ℝ => ((⌊U⌋₊ : ℝ) / U : ℝ)) atTop (𝓝 1)` using `tendsto_nat_floor_div_atTop`. Establish `h2 : Tendsto (fun U : ℝ => ((((⌊U⌋₊ : ℝ) / U : ℝ)) : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ))` using `(Complex.continuous_ofReal.tendsto 1).comp h1`. Establish `h3` using `h0.mul h2`. Rewrite `h3` using `[zero_mul]`.

Use `h3.congr' ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop (1 : ℝ)] with U hU`. Use `show (∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (⌊U⌋₊ : ℂ) * ((((⌊U⌋₊ : ℝ) / U : ℝ)) : ℂ) = (∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (U : ℂ)`. Establish `hf1 : 1 ≤ ⌊U⌋₊` using `(Nat.one_le_floor_iff U).mpr hU`. Establish `hf : (⌊U⌋₊ : ℂ) ≠ 0` using `by exact_mod_cast (show ⌊U⌋₊ ≠ 0 by omega)`.

Establish `e : (⌊U⌋₊ : ℂ) * ((⌊U⌋₊ : ℂ))⁻¹ = 1` using `mul_inv_cancel₀ hf`. Use `push_cast`. Take the linear combination `((∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (U : ℂ)) * e`.
-/
private lemma kronecker_tendsto_zero_real (c : ℕ → ℂ) (S : ℂ)
    (h : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, c n / (n : ℂ)) atTop (𝓝 S)) :
    Tendsto (fun U : ℝ => (∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (U : ℂ)) atTop (𝓝 0) := by
  have h0 := (kronecker_tendsto_zero c S h).comp (tendsto_nat_floor_atTop (α := ℝ))
  have h1 : Tendsto (fun U : ℝ => ((⌊U⌋₊ : ℝ) / U : ℝ)) atTop (𝓝 1) := tendsto_nat_floor_div_atTop
  have h2 : Tendsto (fun U : ℝ => ((((⌊U⌋₊ : ℝ) / U : ℝ)) : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp h1
  have h3 := h0.mul h2
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with U hU
  show (∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (⌊U⌋₊ : ℂ) * ((((⌊U⌋₊ : ℝ) / U : ℝ)) : ℂ) =
    (∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (U : ℂ)
  have hf1 : 1 ≤ ⌊U⌋₊ := (Nat.one_le_floor_iff U).mpr hU
  have hf : (⌊U⌋₊ : ℂ) ≠ 0 := by exact_mod_cast (show ⌊U⌋₊ ≠ 0 by omega)
  have e : (⌊U⌋₊ : ℂ) * ((⌊U⌋₊ : ℂ))⁻¹ = 1 := mul_inv_cancel₀ hf
  push_cast
  linear_combination ((∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (U : ℂ)) * e

/- English proof (translation)
Introduce `a S h y hy`. Use `⟨S - ∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ) + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / (y : ℂ), ?_, ?_⟩` and prove the remaining obligations. Establish `hlim : Tendsto (fun U : ℝ => (∑ n ∈ Icc 1 ⌊U⌋₊, a n / (n : ℂ)) - ∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ) - (∑ n ∈ Icc 1 ⌊U⌋₊, a n) / (U : ℂ) + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / (y : ℂ)) atTop (𝓝 (S - ∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ) - 0 + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / (y : ℂ)))` using `(((h.comp (tendsto_nat_floor_atTop (α := ℝ))).sub_const _).sub (kronecker_tendsto_zero_real a S h)).add_const _`. Rewrite `hlim` using `[sub_zero]`. Use `hlim.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [eventually_ge_atTop y] with U hU`. Conclude with `(integral_partial_sum_div_sq a hy hU).symm`. Establish `hy0 : (y : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr (show (0 : ℝ) < y by linarith).ne'`. Establish `hsum : ∑ n ∈ Icc 1 ⌊y⌋₊, a n * ((y / (n : ℝ) - 1 : ℝ) : ℂ) = (y : ℂ) * (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ)) - ∑ n ∈ Icc 1 ⌊y⌋₊, a n`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e : (y : ℂ) * ((∑ n ∈ Icc 1 ⌊y⌋₊, a n) / (y : ℂ)) = ∑ n ∈ Icc 1 ⌊y⌋₊, a n`. Clear the denominators using the available nonvanishing facts.

Unfold `Gchi`. Rewrite using `[hsum]`. Take the linear combination `e`.
-/
theorem smoothedRemainderIntegralFormula : SmoothedRemainderIntegralFormula := by
  intro a S h y hy
  refine ⟨S - ∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ) + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / (y : ℂ), ?_, ?_⟩
  · have hlim : Tendsto (fun U : ℝ => (∑ n ∈ Icc 1 ⌊U⌋₊, a n / (n : ℂ))
          - ∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ) - (∑ n ∈ Icc 1 ⌊U⌋₊, a n) / (U : ℂ)
          + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / (y : ℂ)) atTop
        (𝓝 (S - ∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ) - 0 + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / (y : ℂ))) :=
      (((h.comp (tendsto_nat_floor_atTop (α := ℝ))).sub_const _).sub
        (kronecker_tendsto_zero_real a S h)).add_const _
    rw [sub_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop y] with U hU
    exact (integral_partial_sum_div_sq a hy hU).symm
  · have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (show (0 : ℝ) < y by linarith).ne'
    have hsum : ∑ n ∈ Icc 1 ⌊y⌋₊, a n * ((y / (n : ℝ) - 1 : ℝ) : ℂ) =
        (y : ℂ) * (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ)) - ∑ n ∈ Icc 1 ⌊y⌋₊, a n := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      push_cast
      ring
    have e : (y : ℂ) * ((∑ n ∈ Icc 1 ⌊y⌋₊, a n) / (y : ℂ)) = ∑ n ∈ Icc 1 ⌊y⌋₊, a n := by
      field_simp
    unfold Gchi
    rw [hsum]
    linear_combination e

/- English proof (translation)
Establish `hy0 : 0 < y` using `by linarith`. Establish `hU0 : 0 < U` using `by linarith`. Establish `hsplit : (fun u : ℝ => (psumR a u - u) / u ^ 2) = fun u : ℝ => (∑ n ∈ Icc 1 ⌊u⌋₊, a n) / u ^ 2 - u⁻¹`. Use function extensionality and compare the values at `u`. Rewrite using `[sub_div, psumR]`.

Use `congr 1`. Break down `eq_or_ne u 0 with h | h` into its components or cases. Simplify using `[h]`. Rewrite using `[pow_two, div_mul_eq_div_div, div_self h, one_div]`. Establish `hA : IntervalIntegrable (fun u : ℝ => (∑ n ∈ Icc 1 ⌊u⌋₊, a n) / u ^ 2) volume y U` using `(intervalIntegrable_iff_integrableOn_Icc_of_le hU).mpr (integrableOn_partial_sum_div_sq (𝕜 := ℝ) a hy)`.

Establish `hinv : IntervalIntegrable (fun u : ℝ => u⁻¹) volume y U`. Use `ContinuousOn.intervalIntegrable (continuousOn_inv₀.mono fun x hx => ?_)` and prove the remaining obligations. Rewrite `hx` using `[Set.uIcc_of_le hU]`. Conclude with `(show (0 : ℝ) < x by linarith [hx.1]).ne'`. Establish `hA_eq : ∫ u in y..U, (∑ n ∈ Icc 1 ⌊u⌋₊, a n) / u ^ 2 = (∑ n ∈ Icc 1 ⌊U⌋₊, a n / (n : ℝ)) - (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ)) - (∑ n ∈ Icc 1 ⌊U⌋₊, a n) / U + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / y` using `integral_partial_sum_div_sq (𝕜 := ℝ) a hy hU`.

Rewrite using `[hsplit, intervalIntegral.integral_sub hA hinv, integral_inv_of_pos hy0 hU0, Real.log_div hU0.ne' hy0.ne', hA_eq]`.
-/
private theorem integral_psumR_sub_div_sq_eq_partial_sums (a : ℕ → ℝ) {y U : ℝ} (hy : 1 ≤ y) (hU : y ≤ U) :
    ∫ u in y..U, (psumR a u - u) / u ^ 2 =
      (∑ n ∈ Icc 1 ⌊U⌋₊, a n / (n : ℝ)) - (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ))
        - (∑ n ∈ Icc 1 ⌊U⌋₊, a n) / U + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / y
        - (Real.log U - Real.log y) := by
  have hy0 : 0 < y := by linarith
  have hU0 : 0 < U := by linarith
  have hsplit : (fun u : ℝ => (psumR a u - u) / u ^ 2) =
      fun u : ℝ => (∑ n ∈ Icc 1 ⌊u⌋₊, a n) / u ^ 2 - u⁻¹ := by
    funext u
    rw [sub_div, psumR]
    congr 1
    rcases eq_or_ne u 0 with h | h
    · simp [h]
    · rw [pow_two, div_mul_eq_div_div, div_self h, one_div]
  have hA : IntervalIntegrable (fun u : ℝ => (∑ n ∈ Icc 1 ⌊u⌋₊, a n) / u ^ 2) volume y U :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hU).mpr
      (integrableOn_partial_sum_div_sq (𝕜 := ℝ) a hy)
  have hinv : IntervalIntegrable (fun u : ℝ => u⁻¹) volume y U := by
    refine ContinuousOn.intervalIntegrable (continuousOn_inv₀.mono fun x hx => ?_)
    rw [Set.uIcc_of_le hU] at hx
    exact (show (0 : ℝ) < x by linarith [hx.1]).ne'
  have hA_eq : ∫ u in y..U, (∑ n ∈ Icc 1 ⌊u⌋₊, a n) / u ^ 2 =
      (∑ n ∈ Icc 1 ⌊U⌋₊, a n / (n : ℝ)) - (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ))
        - (∑ n ∈ Icc 1 ⌊U⌋₊, a n) / U + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / y :=
    integral_partial_sum_div_sq (𝕜 := ℝ) a hy hU
  rw [hsplit, intervalIntegral.integral_sub hA hinv, integral_inv_of_pos hy0 hU0,
    Real.log_div hU0.ne' hy0.ne', hA_eq]

/- English proof (translation)
Introduce `a h y hy`. Use `⟨-1 - Real.eulerMascheroniConstant + (-(∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ)) + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / y + Real.log y), (h.add_const _).congr' ?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop y] with U hU`. Rewrite using `[integral_psumR_sub_div_sq_eq_partial_sums a hy hU, integral_psumR_sub_div_sq_eq_partial_sums a le_rfl (hy.trans hU)]`. Simplify using `only [Nat.floor_one, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, div_one, Real.log_one]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hy0 : y ≠ 0` using `(show (0 : ℝ) < y by linarith).ne'`. Establish `hsum : ∑ n ∈ Icc 1 ⌊y⌋₊, a n * (y / (n : ℝ) - 1) = y * (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ)) - ∑ n ∈ Icc 1 ⌊y⌋₊, a n`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `e : y * ((∑ n ∈ Icc 1 ⌊y⌋₊, a n) / y) = ∑ n ∈ Icc 1 ⌊y⌋₊, a n`. Clear the denominators using the available nonvanishing facts. Unfold `Gone`. Rewrite using `[hsum]`.

Take the linear combination `e`.
-/
theorem smoothedRemainderRealIntegralFormula : SmoothedRemainderRealIntegralFormula := by
  intro a h y hy
  refine ⟨-1 - Real.eulerMascheroniConstant + (-(∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ))
    + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / y + Real.log y), (h.add_const _).congr' ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop y] with U hU
    rw [integral_psumR_sub_div_sq_eq_partial_sums a hy hU, integral_psumR_sub_div_sq_eq_partial_sums a le_rfl (hy.trans hU)]
    simp only [Nat.floor_one, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, div_one,
      Real.log_one]
    ring
  · have hy0 : y ≠ 0 := (show (0 : ℝ) < y by linarith).ne'
    have hsum : ∑ n ∈ Icc 1 ⌊y⌋₊, a n * (y / (n : ℝ) - 1) =
        y * (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ)) - ∑ n ∈ Icc 1 ⌊y⌋₊, a n := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    have e : y * ((∑ n ∈ Icc 1 ⌊y⌋₊, a n) / y) = ∑ n ∈ Icc 1 ⌊y⌋₊, a n := by
      field_simp
    unfold Gone
    rw [hsum]
    linear_combination e

end Formalism.HermitianLattices.GL2PrimeSums
