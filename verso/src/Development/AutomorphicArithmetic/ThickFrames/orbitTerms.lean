import Development.AutomorphicArithmetic.ThickFrames.MarkedLow
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Development.AutomorphicArithmetic.ThickFrames.MarkedLowBounds

open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

/- English proof (translation)
Break down `Nat.eq_zero_or_pos N with hN0 | hNpos` into its components or cases. Substitute `hN0` using the available equality. Simplify using `only [Nat.cast_zero, neg_zero, Real.exp_zero]`. Unfold `Formalism.G0.binUpper`. Establish `hset : Icc 0 G = range (G + 1)`.

Use extensionality with `j`. Simplify using `[Nat.lt_succ_iff]`. Rewrite using `[hset]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `j _`. Expand and normalize the polynomial expressions, which then agree. Use `_ = (δ + (1 - δ)) ^ G := (add_pow δ (1 - δ) G).symm`. Use `_ ≤ 1 := by simp`. Establish `he3 : Real.exp 1 < 3` using `lt_trans Real.exp_one_lt_d9 (by norm_num)`.

Establish `hepos : 0 < Real.exp 1` using `Real.exp_pos 1`. Unfold `Formalism.G0.binUpper`. Establish `hterm : ∀ j ∈ Icc N G, (G.choose j : ℝ) * δ ^ j * (1 - δ) ^ (G - j) ≤ (1 / 6 : ℝ) ^ j`. Introduce `j hj`. Establish `hjN : N ≤ j` using `(Finset.mem_Icc.mp hj).1`.

Establish `hjpos : (0 : ℝ) < j` using `by exact_mod_cast lt_of_lt_of_le hNpos hjN`. Establish `hjne : (j : ℝ) ≠ 0` using `hjpos.ne'`. Establish `hc` using `Nat.choose_le_pow_div (α := ℝ) j G`. Establish `hf` using `Real.pow_div_factorial_le_exp (j : ℝ) hjpos.le j`. Establish `hfpos : (0 : ℝ) < (j.factorial : ℝ)` using `by exact_mod_cast Nat.factorial_pos j`.

Establish `h1d : (1 - δ) ^ (G - j) ≤ 1` using `pow_le_one₀ (by linarith) (by linarith)`. Establish `hNj : (N : ℝ) ≤ j` using `by exact_mod_cast hjN`. Establish `hq : Real.exp 1 * G * δ / j ≤ 1 / 6`. Rewrite using `[div_le_iff₀ hjpos]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hq0 : 0 ≤ Real.exp 1 * G * δ / j` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left h1d` to reduce the goal to its premises. Check the signs of the components of the expression. Use `_ ≤ (G : ℝ) ^ j / j.factorial * δ ^ j := by`.

Rewrite using `[mul_one]`. Conclude with `mul_le_mul_of_nonneg_right hc (by positivity)`. Use `_ = (G * δ / j) ^ j * ((j : ℝ) ^ j / j.factorial) := by`. Rewrite using `[div_pow, mul_pow]`. Clear the denominators using the available nonvanishing facts.

Use `_ ≤ (G * δ / j) ^ j * Real.exp j := mul_le_mul_of_nonneg_left hf (by positivity)`. Use `_ = (Real.exp 1 * G * δ / j) ^ j := by`. Rewrite using `[show Real.exp j = Real.exp 1 ^ j by rw [← Real.exp_nat_mul, mul_one], ← mul_pow]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ (1 / 6) ^ j := pow_le_pow_left₀ hq0 hq j`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : (1 / 3 : ℝ) ≤ Real.exp (-1)`. Rewrite using `[Real.exp_neg, ← one_div, div_le_div_iff₀ (by norm_num) hepos]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hexp : Real.exp (-(N : ℝ)) = Real.exp (-1) ^ N`. Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hexp]`.

Establish `h6 : (1 / 6 : ℝ) ^ N = (1 / 3) ^ N * (1 / 2) ^ N`. Rewrite using `[← mul_pow]`. Evaluate the numerical expressions. Establish `h2 : (1 / 2 : ℝ) ^ N ≤ 1 / 2`. Combine the equalities or inequalities in the displayed calculation.

Establish `h3N : (1 / 3 : ℝ) ^ N ≤ Real.exp (-1) ^ N` using `pow_le_pow_left₀ (by norm_num) h3 N`. Establish `h30 : 0 ≤ (1 / 3 : ℝ) ^ N` using `by positivity`. Establish `hprod` using `mul_le_mul_of_nonneg_left h2 h30`. Rewrite using `[h6, div_le_iff₀ (by norm_num)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem ot_binUpper_le (G N : ℕ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1)
    (hN : 6 * Real.exp 1 * (G : ℝ) * δ ≤ N) :
    Formalism.G0.binUpper G δ N ≤ Real.exp (-(N : ℝ)) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    simp only [Nat.cast_zero, neg_zero, Real.exp_zero]
    unfold Formalism.G0.binUpper
    have hset : Icc 0 G = range (G + 1) := by
      ext j
      simp [Nat.lt_succ_iff]
    rw [hset]
    calc ∑ j ∈ range (G + 1), (G.choose j : ℝ) * δ ^ j * (1 - δ) ^ (G - j)
        = ∑ j ∈ range (G + 1), δ ^ j * (1 - δ) ^ (G - j) * (G.choose j : ℝ) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = (δ + (1 - δ)) ^ G := (add_pow δ (1 - δ) G).symm
      _ ≤ 1 := by simp
  · have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hepos : 0 < Real.exp 1 := Real.exp_pos 1
    unfold Formalism.G0.binUpper
    have hterm : ∀ j ∈ Icc N G, (G.choose j : ℝ) * δ ^ j * (1 - δ) ^ (G - j) ≤ (1 / 6 : ℝ) ^ j := by
      intro j hj
      have hjN : N ≤ j := (Finset.mem_Icc.mp hj).1
      have hjpos : (0 : ℝ) < j := by exact_mod_cast lt_of_lt_of_le hNpos hjN
      have hjne : (j : ℝ) ≠ 0 := hjpos.ne'
      have hc := Nat.choose_le_pow_div (α := ℝ) j G
      have hf := Real.pow_div_factorial_le_exp (j : ℝ) hjpos.le j
      have hfpos : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
      have h1d : (1 - δ) ^ (G - j) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      have hNj : (N : ℝ) ≤ j := by exact_mod_cast hjN
      have hq : Real.exp 1 * G * δ / j ≤ 1 / 6 := by
        rw [div_le_iff₀ hjpos]
        linarith
      have hq0 : 0 ≤ Real.exp 1 * G * δ / j := by positivity
      calc (G.choose j : ℝ) * δ ^ j * (1 - δ) ^ (G - j) ≤ (G.choose j : ℝ) * δ ^ j * 1 := by
            apply mul_le_mul_of_nonneg_left h1d
            positivity
        _ ≤ (G : ℝ) ^ j / j.factorial * δ ^ j := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_right hc (by positivity)
        _ = (G * δ / j) ^ j * ((j : ℝ) ^ j / j.factorial) := by
            rw [div_pow, mul_pow]
            field_simp
        _ ≤ (G * δ / j) ^ j * Real.exp j := mul_le_mul_of_nonneg_left hf (by positivity)
        _ = (Real.exp 1 * G * δ / j) ^ j := by
            rw [show Real.exp j = Real.exp 1 ^ j by rw [← Real.exp_nat_mul, mul_one], ← mul_pow]
            congr 1
            ring
        _ ≤ (1 / 6) ^ j := pow_le_pow_left₀ hq0 hq j
    calc ∑ j ∈ Icc N G, (G.choose j : ℝ) * δ ^ j * (1 - δ) ^ (G - j)
        ≤ ∑ j ∈ Icc N G, (1 / 6 : ℝ) ^ j := Finset.sum_le_sum hterm
      _ = ∑ j ∈ Ico N (G + 1), (1 / 6 : ℝ) ^ j := by rw [Finset.Ico_add_one_right_eq_Icc]
      _ ≤ (1 / 6 : ℝ) ^ N / (1 - 1 / 6) := geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
      _ ≤ Real.exp (-(N : ℝ)) := by
          have h3 : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
            rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (by norm_num) hepos]
            linarith
          have hexp : Real.exp (-(N : ℝ)) = Real.exp (-1) ^ N := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
          rw [hexp]
          have h6 : (1 / 6 : ℝ) ^ N = (1 / 3) ^ N * (1 / 2) ^ N := by
            rw [← mul_pow]
            norm_num
          have h2 : (1 / 2 : ℝ) ^ N ≤ 1 / 2 := by
            calc (1 / 2 : ℝ) ^ N ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hNpos
              _ = 1 / 2 := by norm_num
          have h3N : (1 / 3 : ℝ) ^ N ≤ Real.exp (-1) ^ N := pow_le_pow_left₀ (by norm_num) h3 N
          have h30 : 0 ≤ (1 / 3 : ℝ) ^ N := by positivity
          have hprod := mul_le_mul_of_nonneg_left h2 h30
          rw [h6, div_le_iff₀ (by norm_num)]
          linarith

/- English proof (translation)
Establish `h1` using `(isLittleO_log_rpow_atTop ha).bound (c := 1 / (2 * C)) (by positivity)`. Establish `h2` using `(tendsto_rpow_atTop ha).eventually_ge_atTop (2 * C)`. Establish `h3` using `Filter.eventually_ge_atTop (1 : ℝ)`. Take `⟨x₀, hx⟩` from `Filter.eventually_atTop.1 (h1.and (h2.and h3))`. Use `⟨x₀, fun x hxx => ?_⟩` and prove the remaining obligations.

Take `⟨b1, b2, b3⟩` from `hx x hxx`. Rewrite `b1` using `[Real.norm_of_nonneg (Real.log_nonneg b3), Real.norm_of_nonneg (by positivity)]`. Establish `: C * Real.log x ≤ x ^ a / 2`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem ot_exists_log_le_rpow (C a : ℝ) (hC : 0 < C) (ha : 0 < a) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → C * (Real.log x + 1) ≤ x ^ a := by
  have h1 := (isLittleO_log_rpow_atTop ha).bound (c := 1 / (2 * C)) (by positivity)
  have h2 := (tendsto_rpow_atTop ha).eventually_ge_atTop (2 * C)
  have h3 := Filter.eventually_ge_atTop (1 : ℝ)
  obtain ⟨x₀, hx⟩ := Filter.eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨x₀, fun x hxx => ?_⟩
  obtain ⟨b1, b2, b3⟩ := hx x hxx
  rw [Real.norm_of_nonneg (Real.log_nonneg b3), Real.norm_of_nonneg (by positivity)] at b1
  have : C * Real.log x ≤ x ^ a / 2 := by
    calc C * Real.log x ≤ C * (1 / (2 * C) * x ^ a) := mul_le_mul_of_nonneg_left b1 hC.le
      _ = x ^ a / 2 := by field_simp
  linarith

set_option maxHeartbeats 400000 in
/- English proof (translation)
Introduce `eps Co Lb heps`. Establish `hhv : hE eps = 2 + 8 * eps` using `rfl`. Establish `hhpos : 0 < hE eps` using `by rw [hhv]; linarith`. Establish `hKge : 8 * (hE eps + 2) / eps ≤ (KE eps : ℝ)` using `Nat.le_ceil _`. Establish `hepsK : hE eps + 2 ≤ eps / 8 * (KE eps : ℝ)`.

Rewrite `hKge` using `[div_le_iff₀ heps]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hM0eq : ∀ x : ℝ, Formalism.MainNotions.G.orbitSmallMultiplicity (rE eps) (hE eps) x = ⌈(hE eps + 3) * Real.log x * (10 : ℝ) ^ (6 * rE eps + 1)⌉₊`. Introduce `x`. Unfold `Formalism.MainNotions.G.orbitSmallMultiplicity`.

Rewrite using `[zpow_neg, div_inv_eq_mul]`. Use `norm_cast`. Use `set K := KE eps with hK`. Use `set h := hE eps with hh`. Use `set r := rE eps with hr`.

Use `set P : ℝ := (10 : ℝ) ^ (6 * r + 1) with hP`. Establish `hPpos : 0 < P` using `by positivity`. Use `set A : ℝ := |Co| + 1 with hA`. Use `set B : ℝ := (max Lb 1) ^ K with hB`. Establish `hApos : 0 < A` using `by rw [hA]; positivity`.

Establish `hB1 : 1 ≤ B` using `one_le_pow₀ (le_max_right _ _)`. Use `set C1 : ℝ := (h + 3) * P + 2 with hC1`. Establish `hhP : 0 < (h + 3) * P` using `mul_pos (by linarith) hPpos`. Establish `hC1pos : 0 < C1` using `by rw [hC1]; linarith`. Take `⟨y₀, hy₀⟩` from `ot_exists_log_le_rpow (2 * (6 * (r : ℝ) + 1) * C1) (eps / 8) (mul_pos (by positivity) hC1pos) (by positivity)`.

Use `⟨A * (B + 2), max (max y₀ 1) ((100 : ℝ) ^ (8 / eps)), mul_pos hApos (by linarith), ?_⟩` and prove the remaining obligations. Introduce `x hx n L₂ hn1 hn2 hL`. Establish `hx1 : 1 ≤ x` using `le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)`. Establish `hxy : y₀ ≤ x` using `le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)`. Establish `hx100 : (100 : ℝ) ^ (8 / eps) ≤ x` using `le_trans (le_max_right _ _) hx`.

Establish `hx0 : 0 < x` using `by linarith`. Establish `hlogx : 0 ≤ Real.log x` using `Real.log_nonneg hx1`. Use `set δ := dE eps x with hδ`. Establish `hδv : δ = x ^ (-(eps / 8))` using `rfl`. Establish `hδpos : 0 < δ` using `by rw [hδv]; exact Real.rpow_pos_of_pos hx0 _`.

Establish `hδinv : δ⁻¹ = x ^ (eps / 8)` using `by rw [hδv, Real.rpow_neg hx0.le, inv_inv]`. Establish `hδ100 : δ ≤ 1 / 100`. Establish `h100 : (100 : ℝ) ≤ x ^ (eps / 8)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_mul (by norm_num), show (8 / eps * (eps / 8)) = (1 : ℝ) by field_simp, Real.rpow_one]`.

Use `_ ≤ x ^ (eps / 8) := Real.rpow_le_rpow (by positivity) hx100 (by positivity)`. Use `inv_anti₀ (by norm_num) h100` as an intermediate fact. Rewrite `this` using `[← hδinv, inv_inv]`. Rewrite using `[one_div]`. Conclude with `this`.

Establish `hδ1 : δ ≤ 1` using `by linarith`. Establish `hexpb : ∀ t : ℝ, (h + 3) * Real.log x ≤ t → Real.exp (-t) ≤ x ^ (-(h + 3))`. Introduce `t ht`. Rewrite using `[Real.rpow_def_of_pos hx0]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Establish `hM0ge : (h + 3) * Real.log x * P ≤ (Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ)`. Rewrite using `[hM0eq]`. Conclude with `Nat.le_ceil _`. Establish `hM0le : (Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) ≤ (h + 3) * Real.log x * P + 1`.

Rewrite using `[hM0eq]`. Conclude with `(Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg (by linarith) hlogx) hPpos.le)).le`. Prove the components needed by the constructor for the conclusion. Establish `hu0 : (Formalism.MainNotions.G.goodU δ : ℝ) ≤ 2 * x ^ (eps / 8)`. Establish `hc` using `Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 1 / δ by positivity)`.

Unfold `Formalism.MainNotions.G.goodU`. Establish `h1x : 1 ≤ x ^ (eps / 8)` using `Real.one_le_rpow hx1 (by positivity)`. Rewrite `hc`, the goal using `[one_div, hδinv]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsq : x ^ (eps / 8) * x ^ (eps / 8) = x ^ (eps / 4)`.

Rewrite using `[← Real.rpow_add hx0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hMle : (Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) + 1 ≤ C1 * (Real.log x + 1)`. Rewrite using `[hC1]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hy` using `hy₀ x hxy`. Establish `hxe : 0 ≤ x ^ (eps / 8)` using `Real.rpow_nonneg hx0.le _`. Establish `key : ((Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) + 1) * ((6 * (r : ℝ) + 1) * (Formalism.MainNotions.G.goodU δ : ℝ)) ≤ n`. Combine the equalities or inequalities in the displayed calculation.

Apply `mul_le_mul hMle (mul_le_mul_of_nonneg_left hu0 (by positivity)) (by positivity)` to reduce the goal to its premises. Conclude with `mul_nonneg hC1pos.le (by linarith)`. Use `_ = (2 * (6 * (r : ℝ) + 1) * C1 * (Real.log x + 1)) * x ^ (eps / 8) := by ring`. Use `_ ≤ x ^ (eps / 8) * x ^ (eps / 8) := mul_le_mul_of_nonneg_right hy hxe`. Use `_ = x ^ (eps / 4) := hsq`.

Use `_ ≤ n := hn1`. Conclude with `key` after adjusting the coercions. Establish `hxh : 0 ≤ x ^ h` using `Real.rpow_nonneg hx0.le _`. Establish `hnA : (n : ℝ) ≤ A * x ^ h` using `le_trans hn2 (mul_le_mul_of_nonneg_right (by rw [hA]; linarith [le_abs_self Co]) hxh)`. Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`.

Establish `hd3 : x ^ h * x ^ (-(h + 3)) ≤ x ^ (-2 : ℝ)`. Rewrite using `[← Real.rpow_add hx0]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `hd2 : x ^ h * x ^ (-(h + 2)) ≤ x ^ (-2 : ℝ)`. Rewrite using `[← Real.rpow_add hx0]`.

Conclude with `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `hT1 : (L₂.choose K : ℝ) * δ ^ K ≤ B * x ^ (-(h + 2))`. Establish `hLb : (L₂ : ℝ) ≤ max Lb 1` using `le_trans hL (le_max_left _ _)`. Establish `hc : (L₂.choose K : ℝ) ≤ (L₂ : ℝ) ^ K` using `by exact_mod_cast Nat.choose_le_pow L₂ K`. Establish `hcB : (L₂.choose K : ℝ) ≤ B` using `le_trans hc (pow_le_pow_left₀ (Nat.cast_nonneg _) hLb K)`.

Establish `hδK : δ ^ K ≤ x ^ (-(h + 2))`. Rewrite using `[hδv, ← Real.rpow_mul_natCast hx0.le]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith)`. Conclude with `mul_le_mul hcB hδK (pow_nonneg hδpos.le _) (by linarith)`. Establish `hu` using `markedLow_bounds δ r hδpos hδ100`.

Establish `hT2 : (1 - markedLow δ r (Formalism.MainNotions.G.goodU δ)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity r h x ≤ x ^ (-(h + 3))`. Establish `hq0 : (0 : ℝ) ≤ (1 / 10) ^ (6 * r + 1)` using `by positivity`. Establish `hq1 : (1 / 10 : ℝ) ^ (6 * r + 1) ≤ 1` using `pow_le_one₀ (by norm_num) (by norm_num)`. Establish `hp1 : (1 / 10 : ℝ) ^ (6 * r + 1) * P = 1`. Rewrite using `[hP, ← mul_pow]`.

Evaluate the numerical expressions. Establish `hprod` using `mul_le_mul_of_nonneg_right hM0ge hq0`. Establish `hid : (h + 3) * Real.log x * P * (1 / 10 : ℝ) ^ (6 * r + 1) = (h + 3) * Real.log x`. Rewrite using `[mul_assoc ((h + 3) * Real.log x), mul_comm P, hp1, mul_one]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ x ^ (-(h + 3)) := hexpb _ (by linarith)`. Establish `hN1 : Formalism.MainNotions.G.orbitWindowCount r δ h x - 1 = ⌈max (6 * Real.exp 1 * (Formalism.MainNotions.G.goodG' r δ h x : ℝ) * δ) ((h + 3) * Real.logb 2 x)⌉₊`.

Simplify using `only [Formalism.MainNotions.G.orbitWindowCount, Nat.add_sub_cancel]`. Establish `hT3 : binUpper (Formalism.MainNotions.G.goodG' r δ h x) δ (Formalism.MainNotions.G.orbitWindowCount r δ h x - 1) ≤ x ^ (-(h + 3))`. Rewrite using `[hN1]`. Use `le_trans (ot_binUpper_le _ _ δ hδpos.le hδ1 (le_trans (le_max_left _ _) (Nat.le_ceil _))) ?_` and prove the remaining obligations. Apply `hexpb` to reduce the goal to its premises.

Establish `hl2 : Real.log x ≤ Real.logb 2 x`. Rewrite using `[Real.logb, le_div_iff₀ (Real.log_pos one_lt_two)]`. Use `Real.log_two_lt_d9` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.

Establish `hBx : 0 ≤ B * x ^ (-(h + 2))` using `mul_nonneg (by linarith) (Real.rpow_nonneg hx0.le _)`. Establish `hx3 : 0 ≤ x ^ (-(h + 3))` using `Real.rpow_nonneg hx0.le _`. Establish `e1 : (n : ℝ) * (L₂.choose K : ℝ) * δ ^ K ≤ A * B * x ^ (-2 : ℝ)`. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : (n : ℝ) * (1 - markedLow δ r (Formalism.MainNotions.G.goodU δ)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity r h x ≤ A * x ^ (-2 : ℝ)`.

Combine the equalities or inequalities in the displayed calculation. Establish `e3 : (n : ℝ) * binUpper (Formalism.MainNotions.G.goodG' r δ h x) δ (Formalism.MainNotions.G.orbitWindowCount r δ h x - 1) ≤ A * x ^ (-2 : ℝ)`. Combine the equalities or inequalities in the displayed calculation. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem UpperTheory.BernoulliSumsFrobeniusOrbits.orbit_terms :
    ∀ eps Co Lb : ℝ, 0 < eps → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ x ≥ x₀, ∀ n L₂ : ℕ, x ^ (eps / 4) ≤ (n : ℝ) → (n : ℝ) ≤ Co * x ^ hE eps →
      (L₂ : ℝ) ≤ Lb →
      (Formalism.MainNotions.G.orbitSmallMultiplicity (rE eps) (hE eps) x + 1) * ((6 * rE eps + 1) * Formalism.MainNotions.G.goodU (dE eps x)) ≤ n ∧
      (n : ℝ) * (L₂.choose (KE eps) : ℝ) * dE eps x ^ KE eps +
        n * (1 - markedLow (dE eps x) (rE eps) (Formalism.MainNotions.G.goodU (dE eps x))) ^ Formalism.MainNotions.G.orbitSmallMultiplicity (rE eps) (hE eps) x +
        n * binUpper (Formalism.MainNotions.G.goodG' (rE eps) (dE eps x) (hE eps) x) (dE eps x)
          (Formalism.MainNotions.G.orbitWindowCount (rE eps) (dE eps x) (hE eps) x - 1) ≤ Cb * x ^ (-2 : ℝ) := by
  intro eps Co Lb heps
  have hhv : hE eps = 2 + 8 * eps := rfl
  have hhpos : 0 < hE eps := by rw [hhv]; linarith
  have hKge : 8 * (hE eps + 2) / eps ≤ (KE eps : ℝ) := Nat.le_ceil _
  have hepsK : hE eps + 2 ≤ eps / 8 * (KE eps : ℝ) := by
    rw [div_le_iff₀ heps] at hKge
    linarith
  have hM0eq : ∀ x : ℝ, Formalism.MainNotions.G.orbitSmallMultiplicity (rE eps) (hE eps) x
      = ⌈(hE eps + 3) * Real.log x * (10 : ℝ) ^ (6 * rE eps + 1)⌉₊ := by
    intro x
    unfold Formalism.MainNotions.G.orbitSmallMultiplicity
    rw [zpow_neg, div_inv_eq_mul]
    norm_cast
  set K := KE eps with hK
  set h := hE eps with hh
  set r := rE eps with hr
  set P : ℝ := (10 : ℝ) ^ (6 * r + 1) with hP
  have hPpos : 0 < P := by positivity
  set A : ℝ := |Co| + 1 with hA
  set B : ℝ := (max Lb 1) ^ K with hB
  have hApos : 0 < A := by rw [hA]; positivity
  have hB1 : 1 ≤ B := one_le_pow₀ (le_max_right _ _)
  set C1 : ℝ := (h + 3) * P + 2 with hC1
  have hhP : 0 < (h + 3) * P := mul_pos (by linarith) hPpos
  have hC1pos : 0 < C1 := by rw [hC1]; linarith
  obtain ⟨y₀, hy₀⟩ := ot_exists_log_le_rpow (2 * (6 * (r : ℝ) + 1) * C1) (eps / 8)
    (mul_pos (by positivity) hC1pos) (by positivity)
  refine ⟨A * (B + 2), max (max y₀ 1) ((100 : ℝ) ^ (8 / eps)), mul_pos hApos (by linarith), ?_⟩
  intro x hx n L₂ hn1 hn2 hL
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hxy : y₀ ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hx100 : (100 : ℝ) ^ (8 / eps) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  set δ := dE eps x with hδ
  have hδv : δ = x ^ (-(eps / 8)) := rfl
  have hδpos : 0 < δ := by rw [hδv]; exact Real.rpow_pos_of_pos hx0 _
  have hδinv : δ⁻¹ = x ^ (eps / 8) := by rw [hδv, Real.rpow_neg hx0.le, inv_inv]
  have hδ100 : δ ≤ 1 / 100 := by
    have h100 : (100 : ℝ) ≤ x ^ (eps / 8) := by
      calc (100 : ℝ) = ((100 : ℝ) ^ (8 / eps)) ^ (eps / 8) := by
            rw [← Real.rpow_mul (by norm_num), show (8 / eps * (eps / 8)) = (1 : ℝ) by field_simp,
              Real.rpow_one]
        _ ≤ x ^ (eps / 8) := Real.rpow_le_rpow (by positivity) hx100 (by positivity)
    have := inv_anti₀ (by norm_num) h100
    rw [← hδinv, inv_inv] at this
    rw [one_div]
    exact this
  have hδ1 : δ ≤ 1 := by linarith
  have hexpb : ∀ t : ℝ, (h + 3) * Real.log x ≤ t → Real.exp (-t) ≤ x ^ (-(h + 3)) := by
    intro t ht
    rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hM0ge : (h + 3) * Real.log x * P ≤ (Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) := by
    rw [hM0eq]
    exact Nat.le_ceil _
  have hM0le : (Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) ≤ (h + 3) * Real.log x * P + 1 := by
    rw [hM0eq]
    exact (Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg (by linarith) hlogx) hPpos.le)).le
  constructor
  · have hu0 : (Formalism.MainNotions.G.goodU δ : ℝ) ≤ 2 * x ^ (eps / 8) := by
      have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 1 / δ by positivity)
      unfold Formalism.MainNotions.G.goodU
      have h1x : 1 ≤ x ^ (eps / 8) := Real.one_le_rpow hx1 (by positivity)
      rw [one_div, hδinv] at hc ⊢
      linarith
    have hsq : x ^ (eps / 8) * x ^ (eps / 8) = x ^ (eps / 4) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    have hMle : (Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) + 1 ≤ C1 * (Real.log x + 1) := by
      rw [hC1]
      nlinarith
    have hy := hy₀ x hxy
    have hxe : 0 ≤ x ^ (eps / 8) := Real.rpow_nonneg hx0.le _
    have key : ((Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) + 1) * ((6 * (r : ℝ) + 1) * (Formalism.MainNotions.G.goodU δ : ℝ)) ≤ n := by
      calc _ ≤ (C1 * (Real.log x + 1)) * ((6 * (r : ℝ) + 1) * (2 * x ^ (eps / 8))) := by
            apply mul_le_mul hMle (mul_le_mul_of_nonneg_left hu0 (by positivity)) (by positivity)
            exact mul_nonneg hC1pos.le (by linarith)
        _ = (2 * (6 * (r : ℝ) + 1) * C1 * (Real.log x + 1)) * x ^ (eps / 8) := by ring
        _ ≤ x ^ (eps / 8) * x ^ (eps / 8) := mul_le_mul_of_nonneg_right hy hxe
        _ = x ^ (eps / 4) := hsq
        _ ≤ n := hn1
    exact_mod_cast key
  · have hxh : 0 ≤ x ^ h := Real.rpow_nonneg hx0.le _
    have hnA : (n : ℝ) ≤ A * x ^ h :=
      le_trans hn2 (mul_le_mul_of_nonneg_right (by rw [hA]; linarith [le_abs_self Co]) hxh)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hd3 : x ^ h * x ^ (-(h + 3)) ≤ x ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hd2 : x ^ h * x ^ (-(h + 2)) ≤ x ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hT1 : (L₂.choose K : ℝ) * δ ^ K ≤ B * x ^ (-(h + 2)) := by
      have hLb : (L₂ : ℝ) ≤ max Lb 1 := le_trans hL (le_max_left _ _)
      have hc : (L₂.choose K : ℝ) ≤ (L₂ : ℝ) ^ K := by exact_mod_cast Nat.choose_le_pow L₂ K
      have hcB : (L₂.choose K : ℝ) ≤ B := le_trans hc (pow_le_pow_left₀ (Nat.cast_nonneg _) hLb K)
      have hδK : δ ^ K ≤ x ^ (-(h + 2)) := by
        rw [hδv, ← Real.rpow_mul_natCast hx0.le]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith)
      exact mul_le_mul hcB hδK (pow_nonneg hδpos.le _) (by linarith)
    have hu := markedLow_bounds δ r hδpos hδ100
    have hT2 : (1 - markedLow δ r (Formalism.MainNotions.G.goodU δ)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity r h x ≤ x ^ (-(h + 3)) := by
      have hq0 : (0 : ℝ) ≤ (1 / 10) ^ (6 * r + 1) := by positivity
      have hq1 : (1 / 10 : ℝ) ^ (6 * r + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hp1 : (1 / 10 : ℝ) ^ (6 * r + 1) * P = 1 := by
        rw [hP, ← mul_pow]
        norm_num
      have hprod := mul_le_mul_of_nonneg_right hM0ge hq0
      have hid : (h + 3) * Real.log x * P * (1 / 10 : ℝ) ^ (6 * r + 1) = (h + 3) * Real.log x := by
        rw [mul_assoc ((h + 3) * Real.log x), mul_comm P, hp1, mul_one]
      calc (1 - markedLow δ r (Formalism.MainNotions.G.goodU δ)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity r h x
          ≤ (1 - (1 / 10 : ℝ) ^ (6 * r + 1)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity r h x :=
            pow_le_pow_left₀ (by linarith [hu.2]) (by linarith [hu.1]) _
        _ ≤ Real.exp (-(1 / 10 : ℝ) ^ (6 * r + 1)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity r h x :=
            pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-(1 / 10 : ℝ) ^ (6 * r + 1))]) _
        _ = Real.exp (-((Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) * (1 / 10 : ℝ) ^ (6 * r + 1))) := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
        _ ≤ x ^ (-(h + 3)) := hexpb _ (by linarith)
    have hN1 : Formalism.MainNotions.G.orbitWindowCount r δ h x - 1
        = ⌈max (6 * Real.exp 1 * (Formalism.MainNotions.G.goodG' r δ h x : ℝ) * δ) ((h + 3) * Real.logb 2 x)⌉₊ := by
      simp only [Formalism.MainNotions.G.orbitWindowCount, Nat.add_sub_cancel]
    have hT3 : binUpper (Formalism.MainNotions.G.goodG' r δ h x) δ (Formalism.MainNotions.G.orbitWindowCount r δ h x - 1) ≤ x ^ (-(h + 3)) := by
      rw [hN1]
      refine le_trans (ot_binUpper_le _ _ δ hδpos.le hδ1 (le_trans (le_max_left _ _) (Nat.le_ceil _))) ?_
      apply hexpb
      have hl2 : Real.log x ≤ Real.logb 2 x := by
        rw [Real.logb, le_div_iff₀ (Real.log_pos one_lt_two)]
        have := Real.log_two_lt_d9
        nlinarith
      calc (h + 3) * Real.log x ≤ (h + 3) * Real.logb 2 x := mul_le_mul_of_nonneg_left hl2 (by linarith)
        _ ≤ max (6 * Real.exp 1 * (Formalism.MainNotions.G.goodG' r δ h x : ℝ) * δ) ((h + 3) * Real.logb 2 x) :=
            le_max_right _ _
        _ ≤ _ := Nat.le_ceil _
    have hBx : 0 ≤ B * x ^ (-(h + 2)) := mul_nonneg (by linarith) (Real.rpow_nonneg hx0.le _)
    have hx3 : 0 ≤ x ^ (-(h + 3)) := Real.rpow_nonneg hx0.le _
    have e1 : (n : ℝ) * (L₂.choose K : ℝ) * δ ^ K ≤ A * B * x ^ (-2 : ℝ) := by
      calc (n : ℝ) * (L₂.choose K : ℝ) * δ ^ K = n * ((L₂.choose K : ℝ) * δ ^ K) := by ring
        _ ≤ n * (B * x ^ (-(h + 2))) := mul_le_mul_of_nonneg_left hT1 hn0
        _ ≤ (A * x ^ h) * (B * x ^ (-(h + 2))) := mul_le_mul_of_nonneg_right hnA hBx
        _ = A * B * (x ^ h * x ^ (-(h + 2))) := by ring
        _ ≤ A * B * x ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left hd2 (mul_nonneg hApos.le (by linarith))
    have e2 : (n : ℝ) * (1 - markedLow δ r (Formalism.MainNotions.G.goodU δ)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity r h x ≤ A * x ^ (-2 : ℝ) := by
      calc _ ≤ (n : ℝ) * x ^ (-(h + 3)) := mul_le_mul_of_nonneg_left hT2 hn0
        _ ≤ (A * x ^ h) * x ^ (-(h + 3)) := mul_le_mul_of_nonneg_right hnA hx3
        _ = A * (x ^ h * x ^ (-(h + 3))) := by ring
        _ ≤ A * x ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left hd3 hApos.le
    have e3 : (n : ℝ) * binUpper (Formalism.MainNotions.G.goodG' r δ h x) δ (Formalism.MainNotions.G.orbitWindowCount r δ h x - 1) ≤ A * x ^ (-2 : ℝ) := by
      calc _ ≤ (n : ℝ) * x ^ (-(h + 3)) := mul_le_mul_of_nonneg_left hT3 hn0
        _ ≤ (A * x ^ h) * x ^ (-(h + 3)) := mul_le_mul_of_nonneg_right hnA hx3
        _ = A * (x ^ h * x ^ (-(h + 3))) := by ring
        _ ≤ A * x ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left hd3 hApos.le
    nlinarith
