import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExpGainFromZeroFreeRegion

open Complex MeasureTheory

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Introduce `hP hRS hD hRight c₁ hc₁ hc₁'`. Take `⟨CD, hCD⟩` from `hD c₁ hc₁ hc₁'`. Take `⟨C₀, hC₀, hR⟩` from `hRight`. Take `⟨C, hCdef⟩ : ∃ C : ℝ, C = max CD 0` from `⟨_, rfl⟩`. Establish `hC : 0 ≤ C` using `hCdef ▸ le_max_right _ _`.

Take `⟨A, hAdef⟩ : ∃ A : ℝ, A = 2 * Real.pi * Real.exp 1 * (1 + C₀) + 6 * Real.exp 1 * (C + 1) + 16 * (C / c₁ + 24 / c₁ ^ 2) + 8 / c₁` from `⟨_, rfl⟩`. Establish `hA0 : 0 ≤ A`. Establish `ha1 : 0 ≤ 2 * Real.pi * Real.exp 1 * (1 + C₀)` using `mul_nonneg (by positivity) (by linarith)`. Establish `ha2 : 0 ≤ 6 * Real.exp 1 * (C + 1)` using `mul_nonneg (by positivity) (by linarith)`. Establish `ha3 : 0 ≤ 16 * (C / c₁ + 24 / c₁ ^ 2)` using `mul_nonneg (by norm_num) (add_nonneg (div_nonneg hC hc₁.le) (by positivity))`.

Establish `ha4 : 0 ≤ 8 / c₁` using `by positivity`. Rewrite using `[hAdef]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨c₁ / 4, max (16 * A * (6 * (8 / (2 * c₁)) ^ 3)) (3 * (4 * 12 ^ 3 * A)), by positivity, ?_⟩` and prove the remaining obligations. Introduce `q _ χ B y hχ hE hy hq`.

Establish `hD' : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) → ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2` using `fun s h1 h2 => (hCD q χ B hχ hE s h1 h2).trans (mul_le_mul_of_nonneg_right (hCdef ▸ le_max_left _ _) (sq_nonneg _))`. Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)`. Establish `hy0 : 0 < y` using `by linarith`. Establish `hy1 : 1 ≤ y` using `by linarith`. Establish `hℓpos : 0 < Real.log y` using `Real.log_pos (by linarith)`.

Take `⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt (Real.log y)` from `⟨_, rfl⟩`. Rewrite `hq`, the goal using `[← hsdef]`. Establish `hℓ : Real.log y = s ^ 2` using `by rw [hsdef]; exact (Real.sq_sqrt hℓpos.le).symm`. Establish `hs0 : 0 < s` using `by rw [hsdef]; exact Real.sqrt_pos.mpr hℓpos`. Take `⟨T, hTdef⟩ : ∃ T : ℝ, T = Real.exp (c₁ * s / 2)` from `⟨_, rfl⟩`.

Take `⟨X, hXdef⟩ : ∃ X : ℝ, X = Real.exp (-(c₁ * s / 2))` from `⟨_, rfl⟩`. Establish `hT1 : 1 ≤ T` using `by rw [hTdef]; exact Real.one_le_exp (by positivity)`. Establish `hT0 : 0 < T` using `by linarith`. Establish `hTX : T * X = 1` using `by rw [hTdef, hXdef, ← Real.exp_add]; simp`. Establish `hX0 : 0 < X` using `by rw [hXdef]; exact Real.exp_pos _`.

Establish `hX1 : X ≤ 1`. Rewrite using `[hXdef]; exact Real.exp_le_one_iff.mpr (by linarith [mul_pos hc₁ hs0])`. Take `⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log ((q : ℝ) * (T + 2))` from `⟨_, rfl⟩`. Take `⟨σ₁, hσ₁, hmain⟩` from `chebyshev_character_explicit_general hP hRS c₁ C C₀ hc₁ hc₁' hC hC₀ χ B hχ hE hD' (hR q χ) y T L hy hT1 hLdef.symm`. Establish `hqT1 : (1 : ℝ) ≤ (q : ℝ) * (T + 2)` using `one_le_mul_of_one_le_of_one_le hq1 (by linarith)`.

Establish `hL0 : 0 ≤ L` using `by rw [hLdef]; exact Real.log_nonneg hqT1`. Establish `hlogq : Real.log q ≤ c₁ / 4 * s` using `(Real.log_le_iff_le_exp (by linarith)).mpr hq`. Establish `hlogT : Real.log (T + 2) ≤ 2 + c₁ * s / 2`. Rewrite using `[Real.log_le_iff_le_exp (by linarith), Real.exp_add, ← hTdef]`. Establish `h3 : (3 : ℝ) ≤ Real.exp 2` using `by have := Real.add_one_le_exp (2 : ℝ); linarith`.

Use `mul_le_mul_of_nonneg_right h3 hT0.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLb : L ≤ 3 * c₁ / 4 * s + 2`. Rewrite using `[hLdef, Real.log_mul (by linarith) (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hs'1 : 1 ≤ s + 2` using `by linarith`. Establish `hLs' : L ≤ s + 2`. Establish `: 3 * c₁ / 4 * s ≤ s` using `mul_le_of_le_one_left hs0.le (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hP1 : 1 ≤ (s + 2) ^ 3` using `one_le_pow₀ hs'1`.

Establish `h23 : (s + 2) ^ 2 ≤ (s + 2) ^ 3` using `pow_le_pow_right₀ hs'1 (by norm_num)`. Establish `hℓP : Real.log y ≤ (s + 2) ^ 3`. Rewrite using `[hℓ]`. Establish `h1 : s ^ 2 ≤ (s + 2) ^ 2` using `pow_le_pow_left₀ hs0.le (by linarith) 2`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hL2P : L ^ 2 ≤ (s + 2) ^ 3`. Establish `h1 : L ^ 2 ≤ (s + 2) ^ 2` using `pow_le_pow_left₀ hL0 hLs' 2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL3P : L ^ 3 ≤ (s + 2) ^ 3` using `pow_le_pow_left₀ hL0 hLs' 3`. Establish `hLP : L ≤ (s + 2) ^ 3`.

Establish `: s + 2 ≤ (s + 2) ^ 3` using `le_self_pow₀ hs'1 (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hyσ0 : 0 ≤ y ^ σ₁` using `Real.rpow_nonneg hy0.le _`. Establish `hterms` using `perron_error_terms_sum_bound C C₀ c₁ y T X L ((s + 2) ^ 3) (y ^ σ₁) (Real.log y) hc₁ hC hC₀ hy0 hT1 hTX hL0 hyσ0 hℓP hP1 hL2P hL3P hLP`. Rewrite `hterms` using `[← hAdef]`.

Establish `htot` using `hmain.trans hterms`. Establish `hyX : 0 ≤ y * X` using `by positivity`. Distinguish the cases in `hs : 10 ≤ s`. Establish `hL4 : 4 * L ≤ s`. Use `mul_le_mul_of_nonneg_right hc₁' hs0.le` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLpos : 0 < L`. Rewrite using `[hLdef]`. Apply `Real.log_pos` to reduce the goal to its premises. Use `mul_le_mul hq1 (show (3 : ℝ) ≤ T + 2 by linarith) (by norm_num) (by linarith)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hWX : T * y ^ σ₁ ≤ y * X`. Rewrite using `[hTdef, hXdef]`. Conclude with `exp_gain_from_zero_free_region y s c₁ σ₁ L hy0 hℓ hs0 hc₁ hLpos hL4 hσ₁`. Establish `hs'2 : (s + 2) ^ 3 ≤ 8 * s ^ 3`.

Combine the equalities or inequalities in the displayed calculation. Establish `hX3` using `cube_mul_exp_le_poly_bound c₁ s y X hc₁ hs0 hy0 hXdef`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hs` using `[not_le]`. Take `⟨hT3', hexp⟩` from `small_scale_exp_bounds c₁ s hc₁ hc₁' hs`.

Establish `hT3 : T ≤ 3` using `hTdef ▸ hT3'`. Establish `hPs : (s + 2) ^ 3 ≤ 12 ^ 3` using `pow_le_pow_left₀ (by linarith) (by linarith) 3`. Establish `hσ₁1 : σ₁ ≤ 1`. Establish `: 0 ≤ c₁ / (4 * L)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hyσ : y ^ σ₁ ≤ y`. Use `Real.rpow_le_rpow_of_exponent_le hy1 hσ₁1` as an intermediate fact. Rewrite `this` using `[Real.rpow_one]`. Then use the resulting hypothesis. Establish `hW3 : T * y ^ σ₁ ≤ 3 * y` using `mul_le_mul hT3 hyσ hyσ0 (by norm_num)`. Establish `hyX1 : y * X ≤ y` using `mul_le_of_le_one_right hy0.le hX1`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem smoothed_character_sum_of : SmoothChiOf := by
  intro hP hRS hD hRight c₁ hc₁ hc₁'
  obtain ⟨CD, hCD⟩ := hD c₁ hc₁ hc₁'
  obtain ⟨C₀, hC₀, hR⟩ := hRight
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max CD 0 := ⟨_, rfl⟩
  have hC : 0 ≤ C := hCdef ▸ le_max_right _ _
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 2 * Real.pi * Real.exp 1 * (1 + C₀) + 6 * Real.exp 1 * (C + 1) +
      16 * (C / c₁ + 24 / c₁ ^ 2) + 8 / c₁ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    have ha1 : 0 ≤ 2 * Real.pi * Real.exp 1 * (1 + C₀) := mul_nonneg (by positivity) (by linarith)
    have ha2 : 0 ≤ 6 * Real.exp 1 * (C + 1) := mul_nonneg (by positivity) (by linarith)
    have ha3 : 0 ≤ 16 * (C / c₁ + 24 / c₁ ^ 2) :=
      mul_nonneg (by norm_num) (add_nonneg (div_nonneg hC hc₁.le) (by positivity))
    have ha4 : 0 ≤ 8 / c₁ := by positivity
    rw [hAdef]; linarith
  refine ⟨c₁ / 4, max (16 * A * (6 * (8 / (2 * c₁)) ^ 3)) (3 * (4 * 12 ^ 3 * A)), by positivity, ?_⟩
  intro q _ χ B y hχ hE hy hq
  have hD' : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
      ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 :=
    fun s h1 h2 => (hCD q χ B hχ hE s h1 h2).trans
      (mul_le_mul_of_nonneg_right (hCdef ▸ le_max_left _ _) (sq_nonneg _))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hℓpos : 0 < Real.log y := Real.log_pos (by linarith)
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt (Real.log y) := ⟨_, rfl⟩
  rw [← hsdef] at hq ⊢
  have hℓ : Real.log y = s ^ 2 := by rw [hsdef]; exact (Real.sq_sqrt hℓpos.le).symm
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hℓpos
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = Real.exp (c₁ * s / 2) := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = Real.exp (-(c₁ * s / 2)) := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by rw [hTdef]; exact Real.one_le_exp (by positivity)
  have hT0 : 0 < T := by linarith
  have hTX : T * X = 1 := by rw [hTdef, hXdef, ← Real.exp_add]; simp
  have hX0 : 0 < X := by rw [hXdef]; exact Real.exp_pos _
  have hX1 : X ≤ 1 := by
    rw [hXdef]; exact Real.exp_le_one_iff.mpr (by linarith [mul_pos hc₁ hs0])
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log ((q : ℝ) * (T + 2)) := ⟨_, rfl⟩
  obtain ⟨σ₁, hσ₁, hmain⟩ :=
    chebyshev_character_explicit_general hP hRS c₁ C C₀ hc₁ hc₁' hC hC₀ χ B hχ hE hD' (hR q χ) y T L hy hT1 hLdef.symm

  have hqT1 : (1 : ℝ) ≤ (q : ℝ) * (T + 2) := one_le_mul_of_one_le_of_one_le hq1 (by linarith)
  have hL0 : 0 ≤ L := by rw [hLdef]; exact Real.log_nonneg hqT1
  have hlogq : Real.log q ≤ c₁ / 4 * s := (Real.log_le_iff_le_exp (by linarith)).mpr hq
  have hlogT : Real.log (T + 2) ≤ 2 + c₁ * s / 2 := by
    rw [Real.log_le_iff_le_exp (by linarith), Real.exp_add, ← hTdef]
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
    have := mul_le_mul_of_nonneg_right h3 hT0.le
    linarith
  have hLb : L ≤ 3 * c₁ / 4 * s + 2 := by
    rw [hLdef, Real.log_mul (by linarith) (by linarith)]
    linarith
  have hs'1 : 1 ≤ s + 2 := by linarith
  have hLs' : L ≤ s + 2 := by
    have : 3 * c₁ / 4 * s ≤ s := mul_le_of_le_one_left hs0.le (by linarith)
    linarith
  have hP1 : 1 ≤ (s + 2) ^ 3 := one_le_pow₀ hs'1
  have h23 : (s + 2) ^ 2 ≤ (s + 2) ^ 3 := pow_le_pow_right₀ hs'1 (by norm_num)
  have hℓP : Real.log y ≤ (s + 2) ^ 3 := by
    rw [hℓ]
    have h1 : s ^ 2 ≤ (s + 2) ^ 2 := pow_le_pow_left₀ hs0.le (by linarith) 2
    linarith
  have hL2P : L ^ 2 ≤ (s + 2) ^ 3 := by
    have h1 : L ^ 2 ≤ (s + 2) ^ 2 := pow_le_pow_left₀ hL0 hLs' 2
    linarith
  have hL3P : L ^ 3 ≤ (s + 2) ^ 3 := pow_le_pow_left₀ hL0 hLs' 3
  have hLP : L ≤ (s + 2) ^ 3 := by
    have : s + 2 ≤ (s + 2) ^ 3 := le_self_pow₀ hs'1 (by norm_num)
    linarith
  have hyσ0 : 0 ≤ y ^ σ₁ := Real.rpow_nonneg hy0.le _
  have hterms := perron_error_terms_sum_bound C C₀ c₁ y T X L ((s + 2) ^ 3) (y ^ σ₁) (Real.log y) hc₁ hC hC₀ hy0
    hT1 hTX hL0 hyσ0 hℓP hP1 hL2P hL3P hLP
  rw [← hAdef] at hterms
  have htot := hmain.trans hterms
  have hyX : 0 ≤ y * X := by positivity
  by_cases hs : 10 ≤ s
  ·
    have hL4 : 4 * L ≤ s := by
      have := mul_le_mul_of_nonneg_right hc₁' hs0.le
      linarith
    have hLpos : 0 < L := by
      rw [hLdef]; apply Real.log_pos
      have := mul_le_mul hq1 (show (3 : ℝ) ≤ T + 2 by linarith) (by norm_num) (by linarith)
      linarith
    have hWX : T * y ^ σ₁ ≤ y * X := by
      rw [hTdef, hXdef]; exact exp_gain_from_zero_free_region y s c₁ σ₁ L hy0 hℓ hs0 hc₁ hLpos hL4 hσ₁
    have hs'2 : (s + 2) ^ 3 ≤ 8 * s ^ 3 := by
      calc (s + 2) ^ 3 ≤ (2 * s) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
        _ = 8 * s ^ 3 := by ring
    have hX3 := cube_mul_exp_le_poly_bound c₁ s y X hc₁ hs0 hy0 hXdef
    calc _ ≤ A * (s + 2) ^ 3 * (y * X + T * y ^ σ₁) := htot
      _ ≤ A * (8 * s ^ 3) * (y * X + y * X) := by gcongr
      _ = 16 * A * (s ^ 3 * X * y) := by ring
      _ ≤ 16 * A * (6 * (8 / (2 * c₁)) ^ 3 * (y * Real.exp (-(c₁ / 4) * s))) := by gcongr
      _ = 16 * A * (6 * (8 / (2 * c₁)) ^ 3) * y * Real.exp (-(c₁ / 4) * s) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  ·
    rw [not_le] at hs
    obtain ⟨hT3', hexp⟩ := small_scale_exp_bounds c₁ s hc₁ hc₁' hs
    have hT3 : T ≤ 3 := hTdef ▸ hT3'
    have hPs : (s + 2) ^ 3 ≤ 12 ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    have hσ₁1 : σ₁ ≤ 1 := by
      have : 0 ≤ c₁ / (4 * L) := by positivity
      linarith
    have hyσ : y ^ σ₁ ≤ y := by
      have := Real.rpow_le_rpow_of_exponent_le hy1 hσ₁1
      rwa [Real.rpow_one] at this
    have hW3 : T * y ^ σ₁ ≤ 3 * y := mul_le_mul hT3 hyσ hyσ0 (by norm_num)
    have hyX1 : y * X ≤ y := mul_le_of_le_one_right hy0.le hX1
    calc _ ≤ A * (s + 2) ^ 3 * (y * X + T * y ^ σ₁) := htot
      _ ≤ A * 12 ^ 3 * (y + 3 * y) := by gcongr
      _ = 4 * 12 ^ 3 * A * y * 1 := by ring
      _ ≤ 4 * 12 ^ 3 * A * y * (3 * Real.exp (-(c₁ / 4) * s)) := by gcongr
      _ = 3 * (4 * 12 ^ 3 * A) * y * Real.exp (-(c₁ / 4) * s) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

end Formalism.ZeroFreeDirichlet
