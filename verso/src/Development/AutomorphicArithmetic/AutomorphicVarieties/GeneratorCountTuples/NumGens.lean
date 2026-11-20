import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.Bridge
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealCounting.ClassC

open NumberField UpperTheory.V UpperTheory.V.K

/- English proof (translation)
Introduce `l hl L _ _ a ha`. Establish `hp` using `hl.out`. Establish `hn1 : (1 : ℝ) ≤ (Module.finrank ℚ L : ℝ)`. Conclude with `Module.finrank_pos (R := ℚ) (M := L)` after adjusting the coercions. Establish `hDcast : (((discr L).natAbs : ℕ) : ℝ) = |((discr L : ℤ) : ℝ)|`.

Rewrite using `[Nat.cast_natAbs, Int.cast_abs]`. Establish `hD1 : (1 : ℝ) ≤ |((discr L : ℤ) : ℝ)|`. Rewrite using `[← hDcast]`. Conclude with `Nat.one_le_cast.2 (Int.natAbs_pos.2 (discr_ne_zero L))`. Establish `hX : 0 ≤ Real.log |((discr L : ℤ) : ℝ)|` using `Real.log_nonneg hD1`.

Establish `hY : Real.log (2 * |((discr L : ℤ) : ℝ)|) = Real.log 2 + Real.log |((discr L : ℤ) : ℝ)|` using `Real.log_mul (by norm_num) (by linarith)`. Establish `hl2 : (2 : ℝ) ≤ l` using `by exact_mod_cast hp.two_le`. Establish `hlam : Real.log 2 ≤ Real.log l` using `Real.log_le_log (by norm_num) hl2`. Establish `hlog2` using `Real.log_two_gt_d9`. Establish `hcl` using `KStar.IdealCounting.log_classNumber_le L`.

Establish `hlog1 : Real.log (1 + Real.log |((discr L : ℤ) : ℝ)| / 2) ≤ Real.log |((discr L : ℤ) : ℝ)| / 2`. Use `Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log |((discr L : ℤ) : ℝ)| / 2 by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hh : 0 < classNumber L` using `classNumber_pos L`. Establish `hmain : Real.log a ≤ Real.log (classNumber L) + (Module.finrank ℚ L : ℝ) * Real.log l`.

Break down `Nat.eq_zero_or_pos a with rfl | ha0` into its components or cases. Rewrite using `[Nat.cast_zero, Real.log_zero]`. Conclude with `add_nonneg (Real.log_natCast_nonneg _) (mul_nonneg (by positivity) (Real.log_nonneg (by linarith)))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.log_mul (by exact_mod_cast hh.ne') (by positivity), Real.log_pow]`.

Rewrite using `[hDcast, hY]`. Use `set X := Real.log |((discr L : ℤ) : ℝ)|`. Use `set lam := Real.log (l : ℝ)`. Use `set n := (Module.finrank ℚ L : ℝ)`. Establish `hlam0 : 0 ≤ lam` using `by linarith`.

Establish `ha1 : X / 2 ≤ X * lam` using `by nlinarith`. Establish `ha2 : X * lam ≤ n * (X * lam)` using `by nlinarith [mul_nonneg hX hlam0]`. Establish `ha3 : n * Real.log (1 + X / 2) ≤ n * (X / 2)` using `mul_le_mul_of_nonneg_left hlog1 (by linarith)`. Establish `ha4 : n * lam ≤ 4 * n * Real.log 2 * lam` using `by nlinarith [mul_nonneg (show (0:ℝ) ≤ n by linarith) hlam0]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem UpperTheory.V.K.numGens :
    ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [NumberField L] (a : ℕ), a ≤ classNumber L * l ^ Module.finrank ℚ L → Real.log a ≤ 4 * (Module.finrank ℚ L : ℝ) * Real.log (2 * ((discr L).natAbs : ℝ)) * Real.log l := by
  intro l hl L _ _ a ha
  have hp := hl.out
  have hn1 : (1 : ℝ) ≤ (Module.finrank ℚ L : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := L)
  have hDcast : (((discr L).natAbs : ℕ) : ℝ) = |((discr L : ℤ) : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hD1 : (1 : ℝ) ≤ |((discr L : ℤ) : ℝ)| := by
    rw [← hDcast]
    exact Nat.one_le_cast.2 (Int.natAbs_pos.2 (discr_ne_zero L))
  have hX : 0 ≤ Real.log |((discr L : ℤ) : ℝ)| := Real.log_nonneg hD1
  have hY : Real.log (2 * |((discr L : ℤ) : ℝ)|) = Real.log 2 + Real.log |((discr L : ℤ) : ℝ)| :=
    Real.log_mul (by norm_num) (by linarith)
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hp.two_le
  have hlam : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) hl2
  have hlog2 := Real.log_two_gt_d9
  have hcl := KStar.IdealCounting.log_classNumber_le L
  have hlog1 : Real.log (1 + Real.log |((discr L : ℤ) : ℝ)| / 2) ≤ Real.log |((discr L : ℤ) : ℝ)| / 2 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log |((discr L : ℤ) : ℝ)| / 2 by linarith)
    linarith
  have hh : 0 < classNumber L := classNumber_pos L
  have hmain : Real.log a ≤ Real.log (classNumber L) + (Module.finrank ℚ L : ℝ) * Real.log l := by
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · rw [Nat.cast_zero, Real.log_zero]
      exact add_nonneg (Real.log_natCast_nonneg _) (mul_nonneg (by positivity) (Real.log_nonneg (by linarith)))
    · calc Real.log a ≤ Real.log ((classNumber L : ℝ) * (l : ℝ) ^ Module.finrank ℚ L) :=
            Real.log_le_log (by exact_mod_cast ha0) (by exact_mod_cast ha)
        _ = _ := by
          rw [Real.log_mul (by exact_mod_cast hh.ne') (by positivity), Real.log_pow]
  rw [hDcast, hY]
  set X := Real.log |((discr L : ℤ) : ℝ)|
  set lam := Real.log (l : ℝ)
  set n := (Module.finrank ℚ L : ℝ)
  have hlam0 : 0 ≤ lam := by linarith
  have ha1 : X / 2 ≤ X * lam := by nlinarith
  have ha2 : X * lam ≤ n * (X * lam) := by nlinarith [mul_nonneg hX hlam0]
  have ha3 : n * Real.log (1 + X / 2) ≤ n * (X / 2) := mul_le_mul_of_nonneg_left hlog1 (by linarith)
  have ha4 : n * lam ≤ 4 * n * Real.log 2 * lam := by nlinarith [mul_nonneg (show (0:ℝ) ≤ n by linarith) hlam0]
  nlinarith
