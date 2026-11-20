import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk

/- English proof (translation)
Establish `h1` using `exp_neg_integrableOn_Ioi y ht`. Establish `h2` using `integral_exp_mul_Ioi (a := -t) (by linarith) y`. Simplify using `only [neg_mul] at h1 h2`. Use `⟨h1.const_mul t, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_const_mul, h2]`.

Clear the denominators using the available nonvanishing facts.
-/
lemma integral_mul_exp_neg_Ioi {t : ℝ} (ht : 0 < t) (y : ℝ) :
    IntegrableOn (fun x : ℝ => t * Real.exp (-(t * x))) (Set.Ioi y) ∧
    ∫ x in Set.Ioi y, t * Real.exp (-(t * x)) = Real.exp (-(t * y)) := by
  have h1 := exp_neg_integrableOn_Ioi y ht
  have h2 := integral_exp_mul_Ioi (a := -t) (by linarith) y
  simp only [neg_mul] at h1 h2
  refine ⟨h1.const_mul t, ?_⟩
  rw [integral_const_mul, h2]
  field_simp

/- English proof (translation)
Use `set φ : ℕ → ℝ → ℝ := fun n x => (Set.Ici (n : ℝ)).indicator (fun x => t * Real.exp (-(t * x))) x with hφ`. Establish `hφi : ∀ n, Integrable (φ n) (volume.restrict (Set.Ioi (1 : ℝ)))` using `fun n => (integral_mul_exp_neg_Ioi ht 1).1.indicator measurableSet_Ici`. Establish `hφ0 : ∀ n x, 0 ≤ φ n x` using `fun n x => Set.indicator_nonneg (fun y _ => by positivity) x`. Establish `hφv : ∀ n : ℕ, n ≠ 0 → ∫ x in Set.Ioi (1 : ℝ), φ n x = Real.exp (-(t * n))`. Introduce `n hn`.

Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn`. Rewrite using `[hφ]`. Simplify using `only`. Rewrite using `[setIntegral_indicator measurableSet_Ici, ← (integral_mul_exp_neg_Ioi ht n).2]`. Apply `setIntegral_congr_set` to reduce the goal to its premises.

Establish `e1 : (Set.Ioi (1 : ℝ) : Set ℝ) =ᵐ[volume] Set.Ici 1` using `Ioi_ae_eq_Ici`. Establish `e2 : (Set.Ioi (1 : ℝ) ∩ Set.Ici (n : ℝ) : Set ℝ) =ᵐ[volume] (Set.Ici 1 ∩ Set.Ici (n : ℝ) : Set ℝ)` using `ae_eq_set_inter e1 (ae_eq_refl _)`. Rewrite `e2` using `[Set.Ici_inter_Ici, sup_eq_right.2 hn1]`. Conclude with `e2.trans Ioi_ae_eq_Ici.symm`. Establish `hv : ∀ n : ℕ, ∫ x in Set.Ioi (1 : ℝ), c n * (φ n x : ℂ) = c n * (Real.exp (-(t * n)) : ℂ)`.

Introduce `n`. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[h0]`. Rewrite using `[integral_const_mul, integral_complex_ofReal, hφv n hn]`. Establish `hn : ∀ n : ℕ, ∫ x in Set.Ioi (1 : ℝ), ‖c n * (φ n x : ℂ)‖ = ‖c n‖ * Real.exp (-(t * n))`.

Introduce `n`. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[h0]`. Simplify using `only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hφ0 _ _)]`. Rewrite using `[integral_const_mul, hφv n hn]`.

Establish `key` using `hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Set.Ioi (1 : ℝ))) (F := fun n x => c n * (φ n x : ℂ)) (fun n => ((hφi n).ofReal).const_mul _) (by simpa only [hn] using hs)`. Simplify using `only [hv] at key`. Rewrite using `[key.tsum_eq]`. Apply `setIntegral_congr_fun measurableSet_Ioi` to reduce the goal to its premises. Introduce `x hx`.

Establish `hx0 : (0 : ℝ) ≤ x` using `le_trans zero_le_one (le_of_lt hx)`. Simplify using `only`. Rewrite using `[tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊), Finset.sum_mul]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n hn`.

Establish `: (n : ℝ) ≤ x` using `(Nat.le_floor_iff hx0).1 (Finset.mem_Icc.1 hn).2`. Simplify using `only [hφ]`. Rewrite using `[Set.indicator_of_mem (show x ∈ Set.Ici (n : ℝ) from this)]`. Introduce `n hn`. Break down `eq_or_ne n 0 with rfl | hn0` into its components or cases.

Simplify using `[h0]`. Establish `: ¬ (n : ℝ) ≤ x`. Introduce `h`. Conclude with `hn (Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hn0, (Nat.le_floor_iff hx0).2 h⟩)`. Simplify using `only [hφ]`.

Rewrite using `[Set.indicator_of_notMem (show x ∉ Set.Ici (n : ℝ) from this)]`. Simplify using the standard rewrite rules.
-/
lemma tsum_exp_eq_integral (c : ℕ → ℂ) (h0 : c 0 = 0) {t : ℝ} (ht : 0 < t)
    (hs : Summable (fun n : ℕ => ‖c n‖ * Real.exp (-(t * n)))) :
    ∑' n : ℕ, c n * (Real.exp (-(t * n)) : ℂ) =
      ∫ x in Set.Ioi (1 : ℝ), (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n) * ((t * Real.exp (-(t * x)) : ℝ) : ℂ) := by
  set φ : ℕ → ℝ → ℝ := fun n x => (Set.Ici (n : ℝ)).indicator (fun x => t * Real.exp (-(t * x))) x with hφ
  have hφi : ∀ n, Integrable (φ n) (volume.restrict (Set.Ioi (1 : ℝ))) := fun n =>
    (integral_mul_exp_neg_Ioi ht 1).1.indicator measurableSet_Ici
  have hφ0 : ∀ n x, 0 ≤ φ n x := fun n x =>
    Set.indicator_nonneg (fun y _ => by positivity) x
  have hφv : ∀ n : ℕ, n ≠ 0 → ∫ x in Set.Ioi (1 : ℝ), φ n x = Real.exp (-(t * n)) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    rw [hφ]
    simp only
    rw [setIntegral_indicator measurableSet_Ici, ← (integral_mul_exp_neg_Ioi ht n).2]
    apply setIntegral_congr_set
    have e1 : (Set.Ioi (1 : ℝ) : Set ℝ) =ᵐ[volume] Set.Ici 1 := Ioi_ae_eq_Ici
    have e2 : (Set.Ioi (1 : ℝ) ∩ Set.Ici (n : ℝ) : Set ℝ) =ᵐ[volume] (Set.Ici 1 ∩ Set.Ici (n : ℝ) : Set ℝ) :=
      ae_eq_set_inter e1 (ae_eq_refl _)
    rw [Set.Ici_inter_Ici, sup_eq_right.2 hn1] at e2
    exact e2.trans Ioi_ae_eq_Ici.symm
  have hv : ∀ n : ℕ, ∫ x in Set.Ioi (1 : ℝ), c n * (φ n x : ℂ) = c n * (Real.exp (-(t * n)) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [h0]
    · rw [integral_const_mul, integral_complex_ofReal, hφv n hn]
  have hn : ∀ n : ℕ, ∫ x in Set.Ioi (1 : ℝ), ‖c n * (φ n x : ℂ)‖ = ‖c n‖ * Real.exp (-(t * n)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [h0]
    · simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hφ0 _ _)]
      rw [integral_const_mul, hφv n hn]
  have key := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Set.Ioi (1 : ℝ)))
    (F := fun n x => c n * (φ n x : ℂ)) (fun n => ((hφi n).ofReal).const_mul _)
    (by simpa only [hn] using hs)
  simp only [hv] at key
  rw [key.tsum_eq]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one (le_of_lt hx)
  simp only
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊), Finset.sum_mul]
  · apply Finset.sum_congr rfl
    intro n hn
    have : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0).1 (Finset.mem_Icc.1 hn).2
    simp only [hφ]
    rw [Set.indicator_of_mem (show x ∈ Set.Ici (n : ℝ) from this)]
  · intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [h0]
    · have : ¬ (n : ℝ) ≤ x := by
        intro h
        exact hn (Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hn0, (Nat.le_floor_iff hx0).2 h⟩)
      simp only [hφ]
      rw [Set.indicator_of_notMem (show x ∉ Set.Ici (n : ℝ) from this)]
      simp

/- English proof (translation)
Establish `h` using `Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := x) (by norm_num) hx`. Establish `h2 : ∫ t in Set.Ioi 0, t * Real.exp (-(t * x)) = x ^ (-2 : ℝ)`. Establish `e : (2 : ℝ) - 1 = 1` using `by norm_num`. Simplify using `only [e, Real.rpow_one, Real.Gamma_two, mul_one] at h`. Simplify using `only [mul_comm _ x]`.

Rewrite using `[h, Real.rpow_neg hx.le, one_div, Real.inv_rpow hx.le]`. Use `⟨Integrable.of_integral_ne_zero ?_, h2⟩` and prove the remaining obligations. Rewrite using `[h2]`. Check the signs of the components of the expression.
-/
lemma integral_mul_exp_neg_sq {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(t * x))) (Set.Ioi 0) ∧
    ∫ t in Set.Ioi 0, t * Real.exp (-(t * x)) = x ^ (-2 : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := x) (by norm_num) hx
  have h2 : ∫ t in Set.Ioi 0, t * Real.exp (-(t * x)) = x ^ (-2 : ℝ) := by
    have e : (2 : ℝ) - 1 = 1 := by norm_num
    simp only [e, Real.rpow_one, Real.Gamma_two, mul_one] at h
    simp only [mul_comm _ x]
    rw [h, Real.rpow_neg hx.le, one_div, Real.inv_rpow hx.le]
  refine ⟨Integrable.of_integral_ne_zero ?_, h2⟩
  rw [h2]
  positivity

/- English proof (translation)
Establish `hm : Measurable (Function.uncurry fun (x t : ℝ) => A x * ((t * Real.exp (-(t * x)) : ℝ) : ℂ))`. Unfold `Function.uncurry`. Use `fun_prop`. Establish `hint : Integrable (Function.uncurry fun (x t : ℝ) => A x * ((t * Real.exp (-(t * x)) : ℝ) : ℂ)) ((volume.restrict (Set.Ioi (1 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ))))`. Rewrite using `[integrable_prod_iff hm.aestronglyMeasurable]`.

Prove the components needed by the constructor for the conclusion. Use `filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx`. Establish `hx0 : (0 : ℝ) < x` using `lt_trans zero_lt_one hx`. Conclude with `(Integrable.ofReal (𝕜 := ℂ) (integral_mul_exp_neg_sq hx0).1).const_mul (A x)`. Establish `hb : IntegrableOn (fun x : ℝ => K * x ^ (-(3 / 2) : ℝ)) (Set.Ioi 1)` using `(integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul K`.

Use `Integrable.mono' hb (hm.aestronglyMeasurable.norm.integral_prod_right') ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx`. Establish `hx0 : (0 : ℝ) < x` using `lt_trans zero_lt_one hx`. Establish `e : ∫ t in Set.Ioi (0 : ℝ), ‖A x * ((t * Real.exp (-(t * x)) : ℝ) : ℂ)‖ = ‖A x‖ * x ^ (-2 : ℝ)`. Rewrite using `[← (integral_mul_exp_neg_sq hx0).2, ← integral_const_mul]`.

Apply `setIntegral_congr_fun measurableSet_Ioi` to reduce the goal to its premises. Introduce `t ht`. Establish `ht0 : (0 : ℝ) < t` using `ht`. Simplify using `only`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]`.

Simplify using `only [Function.uncurry]`. Rewrite using `[e, Real.norm_of_nonneg (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hx0]`. Evaluate the numerical expressions.

Rewrite using `[← integral_integral_swap hint]`. Apply `setIntegral_congr_fun measurableSet_Ioi` to reduce the goal to its premises. Introduce `x hx`. Establish `hx0 : (0 : ℝ) < x` using `lt_trans zero_lt_one hx`. Simplify using `only`.

Rewrite using `[integral_const_mul, integral_complex_ofReal, (integral_mul_exp_neg_sq hx0).2, Complex.ofReal_cpow hx0.le]`. Evaluate the numerical expressions.
-/
lemma integral_integral_exp_kernel (A : ℝ → ℂ) (hA : Measurable A) (K : ℝ)
    (hK : ∀ x : ℝ, 1 < x → ‖A x‖ ≤ K * Real.sqrt x) :
    ∫ t in Set.Ioi (0 : ℝ), ∫ x in Set.Ioi (1 : ℝ), A x * ((t * Real.exp (-(t * x)) : ℝ) : ℂ) =
      ∫ x in Set.Ioi (1 : ℝ), A x * (x : ℂ) ^ (-(1 : ℂ) - 1) := by
  have hm : Measurable (Function.uncurry fun (x t : ℝ) => A x * ((t * Real.exp (-(t * x)) : ℝ) : ℂ)) := by
    unfold Function.uncurry
    fun_prop
  have hint : Integrable (Function.uncurry fun (x t : ℝ) => A x * ((t * Real.exp (-(t * x)) : ℝ) : ℂ))
      ((volume.restrict (Set.Ioi (1 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
      exact (Integrable.ofReal (𝕜 := ℂ) (integral_mul_exp_neg_sq hx0).1).const_mul (A x)
    · have hb : IntegrableOn (fun x : ℝ => K * x ^ (-(3 / 2) : ℝ)) (Set.Ioi 1) :=
        (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul K
      refine Integrable.mono' hb (hm.aestronglyMeasurable.norm.integral_prod_right') ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
      have e : ∫ t in Set.Ioi (0 : ℝ), ‖A x * ((t * Real.exp (-(t * x)) : ℝ) : ℂ)‖ = ‖A x‖ * x ^ (-2 : ℝ) := by
        rw [← (integral_mul_exp_neg_sq hx0).2, ← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have ht0 : (0 : ℝ) < t := ht
        simp only
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      simp only [Function.uncurry]
      rw [e, Real.norm_of_nonneg (by positivity)]
      calc ‖A x‖ * x ^ (-2 : ℝ) ≤ K * Real.sqrt x * x ^ (-2 : ℝ) := by
            gcongr; exact hK x hx
        _ = K * x ^ (-(3 / 2) : ℝ) := by
            rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hx0]; norm_num
  rw [← integral_integral_swap hint]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  simp only
  rw [integral_const_mul, integral_complex_ofReal, (integral_mul_exp_neg_sq hx0).2,
    Complex.ofReal_cpow hx0.le]
  norm_num

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using `[𝓕.a_zero]`. Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `h` using `(abs_le.1 (𝓕.count g n hn1)).2`. Rewrite `h` using `[Nat.floor_natCast]`.

Establish `h2 : 𝓕.a g n ≤ ∑ m ∈ Finset.Icc 1 n, 𝓕.a g m` using `Finset.single_le_sum (f := 𝓕.a g) (fun m _ => 𝓕.a_nonneg g m) (Finset.mem_Icc.2 ⟨hn, le_rfl⟩)`. Establish `h3 : Real.sqrt n ≤ n`. Rewrite using `[Real.sqrt_le_left (by positivity)]; nlinarith`. Establish `h4 : 𝓕.κ * n ≤ 4 * n` using `by gcongr; exact 𝓕.κ_le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma LFam.a_le_mul (𝓕 : LFam) (g : 𝓕.G) (n : ℕ) : 𝓕.a g n ≤ 14 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [𝓕.a_zero]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := (abs_le.1 (𝓕.count g n hn1)).2
  rw [Nat.floor_natCast] at h
  have h2 : 𝓕.a g n ≤ ∑ m ∈ Finset.Icc 1 n, 𝓕.a g m :=
    Finset.single_le_sum (f := 𝓕.a g) (fun m _ => 𝓕.a_nonneg g m) (Finset.mem_Icc.2 ⟨hn, le_rfl⟩)
  have h3 : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have h4 : 𝓕.κ * n ≤ 4 * n := by gcongr; exact 𝓕.κ_le
  linarith

/- English proof (translation)
Use `Real.summable_pow_mul_exp_neg_nat_mul 1 ht` as an intermediate fact. Simplify using `using this`.
-/
lemma summable_nat_mul_exp_neg {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => (n : ℝ) * Real.exp (-(t * n))) := by
  have := Real.summable_pow_mul_exp_neg_nat_mul 1 ht
  simpa using this

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma LFam.norm_chi (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (g : 𝓕.G) : ‖χ g‖ = 1 := by
  simp

/- English proof (translation)
Unfold `LFam.aChi`. Combine the equalities or inequalities in the displayed calculation. Use `norm_sum_le_of_le _ fun g _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, 𝓕.norm_chi, one_mul, Complex.norm_real, Real.norm_of_nonneg (𝓕.a_nonneg g n)]`. Conclude with `𝓕.a_le_mul g n`.

Use `_ = Fintype.card 𝓕.G * (14 * n : ℝ) := by simp`. Use `_ ≤ 𝓕.B * (14 * n : ℝ) := by gcongr; exact 𝓕.card_le`. Use `_ = _ := by ring`.
-/
lemma LFam.norm_aChi_le (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (n : ℕ) : ‖𝓕.aChi χ n‖ ≤ 14 * 𝓕.B * n := by
  unfold LFam.aChi
  calc ‖∑ g, χ g * (𝓕.a g n : ℂ)‖ ≤ ∑ g : 𝓕.G, (14 * n : ℝ) := by
        refine norm_sum_le_of_le _ fun g _ => ?_
        rw [norm_mul, 𝓕.norm_chi, one_mul, Complex.norm_real, Real.norm_of_nonneg (𝓕.a_nonneg g n)]
        exact 𝓕.a_le_mul g n
    _ = Fintype.card 𝓕.G * (14 * n : ℝ) := by simp
    _ ≤ 𝓕.B * (14 * n : ℝ) := by gcongr; exact 𝓕.card_le
    _ = _ := by ring

/- English proof (translation)
Rewrite using `[← Finset.sum_mul, AddChar.sum_eq_ite]`. Unfold `LFam.res`. Distinguish the cases in `h : χ = 1`. Rewrite using `[if_pos h, if_pos (show χ = 0 from h)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h, if_neg (show ¬ χ = 0 from h)]`. Simplify using the standard rewrite rules.
-/
lemma LFam.res_eq_sum (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) : 𝓕.res χ = ∑ g, χ g * (𝓕.κ : ℂ) := by
  rw [← Finset.sum_mul, AddChar.sum_eq_ite]
  unfold LFam.res
  by_cases h : χ = 1
  · rw [if_pos h, if_pos (show χ = 0 from h)]; push_cast; ring
  · rw [if_neg h, if_neg (show ¬ χ = 0 from h)]; simp

/- English proof (translation)
Use `Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) ((summable_nat_mul_exp_neg ht).mul_left (14 * 𝓕.B))` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Use `gcongr`. Conclude with `𝓕.norm_aChi_le χ n`.
-/
lemma LFam.summable_norm_aChi_exp (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => ‖𝓕.aChi χ n‖ * Real.exp (-(t * n))) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_nat_mul_exp_neg ht).mul_left (14 * 𝓕.B))
  rw [← mul_assoc]
  gcongr
  exact 𝓕.norm_aChi_le χ n

/- English proof (translation)
Establish `hB : 0 ≤ 𝓕.B` using `le_trans (by norm_num) 𝓕.B_ge`. Establish `hs` using `(summable_nat_mul_exp_neg (t := 1 / 2) (by norm_num)).hasSum.mul_left (14 * 𝓕.B * Real.exp (-(t / 2)))`. Use `(tsum_of_norm_bounded hs fun n => ?_).trans (le_of_eq (by ring))` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases.

Use `𝓕.norm_aChi_le χ 0` as an intermediate fact. Simplify using `using this`. Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `: Real.exp (-(t * n)) ≤ Real.exp (-(t / 2)) * Real.exp (-(1 / 2 * n))`. Rewrite using `[← Real.exp_add]`.

Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.
-/
lemma LFam.norm_theta_large (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {t : ℝ} (ht : 1 ≤ t) :
    ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ)‖ ≤
      (14 * ∑' n : ℕ, (n : ℝ) * Real.exp (-(1 / 2 * n))) * 𝓕.B * Real.exp (-(t / 2)) := by
  have hB : 0 ≤ 𝓕.B := le_trans (by norm_num) 𝓕.B_ge
  have hs := (summable_nat_mul_exp_neg (t := 1 / 2) (by norm_num)).hasSum.mul_left
    (14 * 𝓕.B * Real.exp (-(t / 2)))
  refine (tsum_of_norm_bounded hs fun n => ?_).trans (le_of_eq (by ring))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := 𝓕.norm_aChi_le χ 0
    simpa using this
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : Real.exp (-(t * n)) ≤ Real.exp (-(t / 2)) * Real.exp (-(1 / 2 * n)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  calc ‖𝓕.aChi χ n‖ * Real.exp (-(t * n))
      ≤ (14 * 𝓕.B * n) * (Real.exp (-(t / 2)) * Real.exp (-(1 / 2 * n))) := by
        gcongr; exact 𝓕.norm_aChi_le χ n
    _ = _ := by ring

/- English proof (translation)
Establish `hB : 0 ≤ 𝓕.B` using `le_trans (by norm_num) 𝓕.B_ge`. Establish `hs : ∀ g, Summable (fun n : ℕ => 𝓕.a g n * Real.exp (-(t * n)))` using `fun g => by`. Use `Summable.of_nonneg_of_le (fun n => mul_nonneg (𝓕.a_nonneg g n) (Real.exp_pos _).le) (fun n => ?_) ((summable_nat_mul_exp_neg ht).mul_left 14)` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Use `gcongr`.

Conclude with `𝓕.a_le_mul g n`. Establish `h1 : HasSum (fun n : ℕ => ∑ g, χ g * ((𝓕.a g n * Real.exp (-(t * n)) : ℝ) : ℂ)) (∑ g, χ g * ((∑' n : ℕ, 𝓕.a g n * Real.exp (-(t * n)) : ℝ) : ℂ))` using `hasSum_sum fun g _ => (Complex.hasSum_ofReal.2 (hs g).hasSum).mul_left _`. Establish `h2 : ∀ n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) = ∑ g, χ g * ((𝓕.a g n * Real.exp (-(t * n)) : ℝ) : ℂ)` using `fun n => by`. Unfold `LFam.aChi`. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.ofReal_mul, mul_assoc]`. Simplify using `only [h2]`. Rewrite using `[h1.tsum_eq, 𝓕.res_eq_sum, Finset.sum_div, ← Finset.sum_sub_distrib]`. Combine the equalities or inequalities in the displayed calculation.

Use `norm_sum_le_of_le _ fun g _ => ?_` and prove the remaining obligations. Rewrite using `[mul_div_assoc, ← mul_sub, norm_mul, 𝓕.norm_chi, one_mul, ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `𝓕.theta g t ht ht1`. Use `_ = Fintype.card 𝓕.G * (𝓕.B ^ 10 * t) := by simp`. Use `_ ≤ 𝓕.B * (𝓕.B ^ 10 * t) := by gcongr; exact 𝓕.card_le`.

Use `_ = _ := by ring`.
-/
lemma LFam.norm_theta_small (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) - 𝓕.res χ / t‖ ≤ 𝓕.B ^ 11 * t := by
  have hB : 0 ≤ 𝓕.B := le_trans (by norm_num) 𝓕.B_ge
  have hs : ∀ g, Summable (fun n : ℕ => 𝓕.a g n * Real.exp (-(t * n))) := fun g => by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (𝓕.a_nonneg g n) (Real.exp_pos _).le) (fun n => ?_)
      ((summable_nat_mul_exp_neg ht).mul_left 14)
    rw [← mul_assoc]
    gcongr
    exact 𝓕.a_le_mul g n
  have h1 : HasSum (fun n : ℕ => ∑ g, χ g * ((𝓕.a g n * Real.exp (-(t * n)) : ℝ) : ℂ))
      (∑ g, χ g * ((∑' n : ℕ, 𝓕.a g n * Real.exp (-(t * n)) : ℝ) : ℂ)) :=
    hasSum_sum fun g _ => (Complex.hasSum_ofReal.2 (hs g).hasSum).mul_left _
  have h2 : ∀ n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) =
      ∑ g, χ g * ((𝓕.a g n * Real.exp (-(t * n)) : ℝ) : ℂ) := fun n => by
    unfold LFam.aChi
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Complex.ofReal_mul, mul_assoc]
  simp only [h2]
  rw [h1.tsum_eq, 𝓕.res_eq_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ g : 𝓕.G, 𝓕.B ^ 10 * t := by
        refine norm_sum_le_of_le _ fun g _ => ?_
        rw [mul_div_assoc, ← mul_sub, norm_mul, 𝓕.norm_chi, one_mul, ← Complex.ofReal_div,
          ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact 𝓕.theta g t ht ht1
    _ = Fintype.card 𝓕.G * (𝓕.B ^ 10 * t) := by simp
    _ ≤ 𝓕.B * (𝓕.B ^ 10 * t) := by gcongr; exact 𝓕.card_le
    _ = _ := by ring

/- English proof (translation)
Unfold `LFam.aChi`. Rewrite using `[Finset.sum_comm, 𝓕.res_eq_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Combine the equalities or inequalities in the displayed calculation. Use `norm_sum_le_of_le _ fun g _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, mul_assoc, ← mul_sub, norm_mul, 𝓕.norm_chi, one_mul, ← Complex.ofReal_sum, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]`.

Conclude with `𝓕.count g x hx`. Use `_ = Fintype.card 𝓕.G * (10 * Real.sqrt x) := by simp`. Use `_ ≤ 𝓕.B * (10 * Real.sqrt x) := by gcongr; exact 𝓕.card_le`. Use `_ = _ := by ring`.
-/
lemma LFam.norm_sum_aChi_sub_le (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 𝓕.aChi χ n - 𝓕.res χ * x‖ ≤ 10 * 𝓕.B * Real.sqrt x := by
  unfold LFam.aChi
  rw [Finset.sum_comm, 𝓕.res_eq_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ g : 𝓕.G, 10 * Real.sqrt x := by
        refine norm_sum_le_of_le _ fun g _ => ?_
        rw [← Finset.mul_sum, mul_assoc, ← mul_sub, norm_mul, 𝓕.norm_chi, one_mul, ← Complex.ofReal_sum,
          ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact 𝓕.count g x hx
    _ = Fintype.card 𝓕.G * (10 * Real.sqrt x) := by simp
    _ ≤ 𝓕.B * (10 * Real.sqrt x) := by gcongr; exact 𝓕.card_le
    _ = _ := by ring

/- English proof (translation)
Establish `hr : 𝓕.res χ = 0` using `by unfold LFam.res; rw [if_neg hχ]`. Establish `h0 : 𝓕.aChi χ 0 = 0` using `by simp [LFam.aChi, 𝓕.a_zero]`. Establish `hm : Measurable fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 𝓕.aChi χ n` using `(measurable_from_top (f := fun k : ℕ => ∑ n ∈ Finset.Icc 1 k, 𝓕.aChi χ n)).comp Nat.measurable_floor`. Establish `h` using `integral_integral_exp_kernel _ hm (10 * 𝓕.B) (fun x hx => by`. Use `𝓕.norm_sum_aChi_sub_le χ hx.le` as an intermediate fact.

Rewrite using `[hr, zero_mul, sub_zero] at this)` and apply the resulting hypothesis. Unfold `LFam.F LFam.mel`. Rewrite using `[if_neg hχ, one_mul]`. Simplify using `only [hr, zero_mul, sub_zero]`. Rewrite using `[← h]`.

Apply `setIntegral_congr_fun measurableSet_Ioi` to reduce the goal to its premises. Introduce `t ht`. Conclude with `tsum_exp_eq_integral _ h0 ht (𝓕.summable_norm_aChi_exp χ ht)`.
-/
lemma LFam.integral_theta (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (hχ : χ ≠ 1) :
    ∫ t in Set.Ioi (0 : ℝ), ∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) = 𝓕.F χ 1 := by
  have hr : 𝓕.res χ = 0 := by unfold LFam.res; rw [if_neg hχ]
  have h0 : 𝓕.aChi χ 0 = 0 := by simp [LFam.aChi, 𝓕.a_zero]
  have hm : Measurable fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 𝓕.aChi χ n :=
    (measurable_from_top (f := fun k : ℕ => ∑ n ∈ Finset.Icc 1 k, 𝓕.aChi χ n)).comp Nat.measurable_floor
  have h := integral_integral_exp_kernel _ hm (10 * 𝓕.B) (fun x hx => by
    have := 𝓕.norm_sum_aChi_sub_le χ hx.le
    rwa [hr, zero_mul, sub_zero] at this)
  unfold LFam.F LFam.mel
  rw [if_neg hχ, one_mul]
  simp only [hr, zero_mul, sub_zero]
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact tsum_exp_eq_integral _ h0 ht (𝓕.summable_norm_aChi_exp χ ht)

/- English proof (translation)
Use `set S : ℝ := 14 * ∑' n : ℕ, (n : ℝ) * Real.exp (-(1 / 2 * n)) with hS`. Establish `hS0 : 0 ≤ S` using `mul_nonneg (by norm_num) (tsum_nonneg fun n => by positivity)`. Use `⟨2 * S + 4, by positivity, fun 𝓕 χ => ⟨fun t ht => ⟨𝓕.summable_norm_aChi_exp χ ht, ?_⟩, fun hχ => ⟨fun t ht => ?_, 𝓕.integral_theta χ hχ⟩⟩⟩` and prove the remaining obligations. Establish `hB : 1 ≤ 𝓕.B` using `le_trans (by norm_num) 𝓕.B_ge`. Break down `le_total t 1 with h1 | h1` into its components or cases.

Establish `: t ≤ 1 / t` using `by rw [le_div_iff₀ ht]; nlinarith`. Rewrite using `[min_eq_left this]`. Use `(𝓕.norm_theta_small χ ht h1).trans ?_` and prove the remaining obligations. Establish `: 0 ≤ 𝓕.B ^ 11 * t` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Establish `: 1 / t ≤ t` using `by rw [div_le_iff₀ ht]; nlinarith`. Rewrite using `[min_eq_right this]`. Establish `e1 : Real.exp (-(t / 2)) ≤ 2 * (1 / t)`. Use `Real.add_one_le_exp (t / 2)` as an intermediate fact. Rewrite using `[Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]`.

Establish `e : (2 * (1 / t))⁻¹ = t / 2` using `by field_simp`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hκ : 0 ≤ 𝓕.κ` using `le_trans (by positivity) 𝓕.κ_ge`. Establish `e2 : ‖𝓕.res χ‖ ≤ 4 * 𝓕.B`. Unfold `LFam.res`.

Use `split_ifs`. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg (by positivity)]`. Conclude with `mul_le_mul 𝓕.κ_le 𝓕.card_le (by positivity) (by norm_num)`. Rewrite using `[norm_zero]`. Check the signs of the components of the expression.

Establish `e3 : 𝓕.B ≤ 𝓕.B ^ 11` using `le_self_pow₀ hB (by norm_num)`. Combine the equalities or inequalities in the displayed calculation. Use `(norm_sub_le _ _).trans (add_le_add (𝓕.norm_theta_large χ h1) (le_of_eq ?_))` and prove the remaining obligations. Rewrite using `[norm_div, Complex.norm_real, Real.norm_of_nonneg ht.le, mul_one_div]`. Use `_ ≤ S * 𝓕.B * (2 * (1 / t)) + 4 * 𝓕.B * (1 / t) := by gcongr`.

Use `_ = (2 * S + 4) * 𝓕.B * (1 / t) := by ring`. Use `_ ≤ _ := by gcongr`. Establish `hB : 0 ≤ 𝓕.B` using `le_trans (by norm_num) 𝓕.B_ge`. Use `(𝓕.norm_theta_large χ ht).trans ?_` and prove the remaining obligations. Use `gcongr`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem LFam.exp_sum_bounds : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), (∀ t : ℝ, 0 < t → Summable (fun n : ℕ => ‖𝓕.aChi χ n‖ * Real.exp (-(t * n))) ∧ ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) - 𝓕.res χ / t‖ ≤ C * 𝓕.B ^ 11 * min t (1 / t)) ∧ (χ ≠ 1 → (∀ t : ℝ, 1 ≤ t → ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ)‖ ≤ C * 𝓕.B * Real.exp (-(t / 2))) ∧ ∫ t in Set.Ioi (0 : ℝ), ∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) = 𝓕.F χ 1) := by
  set S : ℝ := 14 * ∑' n : ℕ, (n : ℝ) * Real.exp (-(1 / 2 * n)) with hS
  have hS0 : 0 ≤ S := mul_nonneg (by norm_num) (tsum_nonneg fun n => by positivity)
  refine ⟨2 * S + 4, by positivity, fun 𝓕 χ => ⟨fun t ht => ⟨𝓕.summable_norm_aChi_exp χ ht, ?_⟩,
    fun hχ => ⟨fun t ht => ?_, 𝓕.integral_theta χ hχ⟩⟩⟩
  · have hB : 1 ≤ 𝓕.B := le_trans (by norm_num) 𝓕.B_ge
    rcases le_total t 1 with h1 | h1
    · have : t ≤ 1 / t := by rw [le_div_iff₀ ht]; nlinarith
      rw [min_eq_left this]
      refine (𝓕.norm_theta_small χ ht h1).trans ?_
      have : 0 ≤ 𝓕.B ^ 11 * t := by positivity
      nlinarith
    · have : 1 / t ≤ t := by rw [div_le_iff₀ ht]; nlinarith
      rw [min_eq_right this]
      have e1 : Real.exp (-(t / 2)) ≤ 2 * (1 / t) := by
        have := Real.add_one_le_exp (t / 2)
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
        have e : (2 * (1 / t))⁻¹ = t / 2 := by field_simp
        linarith
      have hκ : 0 ≤ 𝓕.κ := le_trans (by positivity) 𝓕.κ_ge
      have e2 : ‖𝓕.res χ‖ ≤ 4 * 𝓕.B := by
        unfold LFam.res
        split_ifs
        · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          exact mul_le_mul 𝓕.κ_le 𝓕.card_le (by positivity) (by norm_num)
        · rw [norm_zero]; positivity
      have e3 : 𝓕.B ≤ 𝓕.B ^ 11 := le_self_pow₀ hB (by norm_num)
      calc _ ≤ S * 𝓕.B * Real.exp (-(t / 2)) + ‖𝓕.res χ‖ * (1 / t) := by
            refine (norm_sub_le _ _).trans (add_le_add (𝓕.norm_theta_large χ h1) (le_of_eq ?_))
            rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht.le, mul_one_div]
        _ ≤ S * 𝓕.B * (2 * (1 / t)) + 4 * 𝓕.B * (1 / t) := by gcongr
        _ = (2 * S + 4) * 𝓕.B * (1 / t) := by ring
        _ ≤ _ := by gcongr
  · have hB : 0 ≤ 𝓕.B := le_trans (by norm_num) 𝓕.B_ge
    refine (𝓕.norm_theta_large χ ht).trans ?_
    gcongr
    linarith

end GlobalTheory.Hk
