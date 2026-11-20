import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CNDefs

open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder

namespace Formalism.MainNotions.LeviCoordinates

/- English proof (translation)
Introduce `C hC`. Establish `hLc : 0 ≤ Real.log C` using `Real.log_nonneg hC`. Use `⟨max 16 ⌈Real.exp (14 * (1 + Real.log C))⌉₊, ?_⟩` and prove the remaining obligations. Introduce `n p q J a f dN v res ℓ hn hpq hq ha haJ hJq hf hdN hv hℓ hlℓ hres0 hres`. Establish `hn16 : (16:ℝ) ≤ n` using `by exact_mod_cast (le_max_left _ _).trans hn`.

Establish `hn1 : Real.exp (14 * (1 + Real.log C)) ≤ n` using `Nat.ceil_le.mp ((le_max_right _ _).trans hn)`. Establish `hn0 : (0:ℝ) < n` using `by linarith`. Establish `hlog : 14 * (1 + Real.log C) ≤ Real.log n` using `(Real.le_log_iff_exp_le hn0).mpr hn1`. Establish `hC0 : 0 < C` using `by linarith`. Establish `hss : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = n` using `Real.mul_self_sqrt hn0.le`.

Establish `hs4 : 4 ≤ Real.sqrt (n:ℝ)` using `Real.le_sqrt_of_sq_le (by`. Establish `: (4:ℝ) ^ 2 = 16` using `by norm_num`. Use the proof step `linarith)`. Establish `hqs : (q:ℝ) ≤ Real.sqrt (n:ℝ)` using `Real.le_sqrt_of_sq_le (by exact_mod_cast hq)`. Generalize the expression as in `Real.sqrt (n:ℝ) = s at *`.

Establish `hsn : s ≤ n / 4` using `by nlinarith`. Establish `hpr : (p:ℝ) = n - q`. Establish `: ((p + q : ℕ):ℝ) = n` using `by exact_mod_cast hpq`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hJq' : (J:ℝ) ≤ q` using `by exact_mod_cast hJq`. Establish `hJ1 : (1:ℝ) ≤ J` using `by exact_mod_cast ha.trans haJ`. Establish `hf0 : (0:ℝ) ≤ f` using `Nat.cast_nonneg _`. Establish `hJp : J ≤ p`. Establish `: (J:ℝ) ≤ p` using `by linarith`.

Conclude with `this` after adjusting the coercions. Establish `hpJ : ((p - J : ℕ):ℝ) = p - J` using `Nat.cast_sub hJp`. Establish `hp0 : (0:ℝ) < p` using `by linarith`. Establish `t1 : v ^ (-((f:ℝ) * dN / 2)) ≤ Real.exp ((J:ℝ) * n * f)`. Establish `hv0 : 0 < v` using `by linarith`.

Rewrite using `[Real.rpow_def_of_pos hv0]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hlv : 0 ≤ Real.log v + 1`. Establish `h1 : Real.log (1/2) ≤ Real.log v` using `Real.log_le_log (by norm_num) hv`. Establish `h2 : Real.log (1/2) = - Real.log 2` using `by rw [one_div, Real.log_inv]`.

Use `Real.log_two_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd : (dN:ℝ) ≤ 2 * J * n` using `by exact_mod_cast hdN`. Establish `h3 : 0 ≤ (f:ℝ) * dN / 2` using `by positivity`. Establish `h4 : (f:ℝ) * dN / 2 ≤ J * n * f`.

Combine the equalities or inequalities in the displayed calculation. Use polynomial arithmetic with `[mul_nonneg hlv h3]`. Establish `t2 : C ^ (J * n * f) = Real.exp ((J:ℝ) * n * f * Real.log C)`. Rewrite using `[← Real.rpow_natCast, Real.rpow_def_of_pos hC0]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `t3 : res ^ a ≤ Real.exp (2 * f * J * (Real.log C + n))`. Establish `hCl : 0 < C * ℓ` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos hCl, mul_comm]`. Use `_ ≤ _ := by`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Rewrite using `[Real.log_mul hC0.ne' hℓ.ne']`. Use `push_cast`.

Establish `ha' : (a:ℝ) ≤ J` using `by exact_mod_cast haJ`. Establish `h0 : 0 ≤ Real.log C + n` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Establish `t4 : (C / (p:ℝ)) ^ (J * (p - J)) ≤ Real.exp (-((J:ℝ) * n / 2 * (Real.log n - 1 - Real.log C)))`. Establish `hCp : 0 < C / (p:ℝ)` using `by positivity`.

Rewrite using `[← Real.rpow_natCast, Real.rpow_def_of_pos hCp]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Rewrite using `[Real.log_div hC0.ne' hp0.ne', Nat.cast_mul, hpJ]`. Establish `hlp : Real.log n - 1 ≤ Real.log p`. Establish `h1 : Real.log (n / 2) ≤ Real.log p` using `Real.log_le_log (by positivity) (by linarith)`.

Rewrite `h1` using `[Real.log_div hn0.ne' (by norm_num)]`. Use `Real.log_two_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl : 0 ≤ Real.log n - 1 - Real.log C` using `by linarith`. Establish `hk : (J:ℝ) * n / 2 ≤ J * (p - J)`.

Establish `: (n:ℝ) / 2 ≤ p - J` using `by linarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hk0 : 0 ≤ (J:ℝ) * (p - J)` using `le_trans (by positivity) hk`. Establish `a1 : (Real.log C - Real.log p) * ((J:ℝ) * (p - J)) ≤ (-(Real.log n - 1 - Real.log C)) * ((J:ℝ) * (p - J))` using `mul_le_mul_of_nonneg_right (by linarith) hk0`. Establish `a2` using `mul_le_mul_of_nonneg_left hk hl`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `t5 : (J:ℝ) ^ ((J:ℝ) ^ 2 / 2) ≤ Real.exp ((J:ℝ) * n / 8 * Real.log n)`. Rewrite using `[Real.rpow_def_of_pos (by linarith)]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hlJ : Real.log J ≤ Real.log n` using `Real.log_le_log (by linarith) (by linarith)`.

Establish `hlJ0 : 0 ≤ Real.log J` using `Real.log_nonneg hJ1`. Establish `hJ2 : (J:ℝ) ^ 2 / 2 ≤ J * n / 8` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Establish `hv0 : 0 < v` using `by linarith`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[t2]`. Use `gcongr`. Use `_ = Real.exp ((J:ℝ) * n * f + (J:ℝ) * n * f * Real.log C + 2 * f * J * (Real.log C + n) + f * (-((J:ℝ) * n / 2 * (Real.log n - 1 - Real.log C)) + (J:ℝ) * n / 8 * Real.log n)) := by`. Rewrite using `[← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]`. Use `_ ≤ _ := by`.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hw : 0 ≤ (J:ℝ) * n * f` using `by positivity`. Establish `h2 : (f:ℝ) * J * Real.log C * 1 ≤ (f:ℝ) * J * Real.log C * n` using `by gcongr; linarith`. Establish `h3 : (J:ℝ) * n * f * (14 * (1 + Real.log C)) ≤ (J:ℝ) * n * f * Real.log n` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cn_kappaBoundAbs : ∀ C : ℝ, 1 ≤ C → ∃ n₀ : ℕ, ∀ (n p q J a f dN : ℕ) (v res ℓ : ℝ), n₀ ≤ n → p + q = n → q ^ 2 ≤ n →
    1 ≤ a → a ≤ J → J ≤ q → 1 ≤ f → dN ≤ 2 * J * n → 1 / 2 ≤ v → 0 < ℓ → Real.log ℓ ≤ n → 0 ≤ res →
    res ≤ (C * ℓ) ^ (2 * f) →
    v ^ (-((f : ℝ) * dN / 2)) * C ^ (J * n * f) * res ^ a * ((C / p) ^ (J * (p - J)) * (J : ℝ) ^ ((J : ℝ) ^ 2 / 2)) ^ f ≤
      Real.exp (-(1 / 8 * J * n * f * Real.log n)) := by
  intro C hC
  have hLc : 0 ≤ Real.log C := Real.log_nonneg hC
  refine ⟨max 16 ⌈Real.exp (14 * (1 + Real.log C))⌉₊, ?_⟩
  intro n p q J a f dN v res ℓ hn hpq hq ha haJ hJq hf hdN hv hℓ hlℓ hres0 hres
  have hn16 : (16:ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
  have hn1 : Real.exp (14 * (1 + Real.log C)) ≤ n := Nat.ceil_le.mp ((le_max_right _ _).trans hn)
  have hn0 : (0:ℝ) < n := by linarith
  have hlog : 14 * (1 + Real.log C) ≤ Real.log n := (Real.le_log_iff_exp_le hn0).mpr hn1
  have hC0 : 0 < C := by linarith
  have hss : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = n := Real.mul_self_sqrt hn0.le
  have hs4 : 4 ≤ Real.sqrt (n:ℝ) := Real.le_sqrt_of_sq_le (by
    have : (4:ℝ) ^ 2 = 16 := by norm_num
    linarith)
  have hqs : (q:ℝ) ≤ Real.sqrt (n:ℝ) := Real.le_sqrt_of_sq_le (by exact_mod_cast hq)
  generalize Real.sqrt (n:ℝ) = s at *
  have hsn : s ≤ n / 4 := by nlinarith
  have hpr : (p:ℝ) = n - q := by
    have : ((p + q : ℕ):ℝ) = n := by exact_mod_cast hpq
    push_cast at this; linarith
  have hJq' : (J:ℝ) ≤ q := by exact_mod_cast hJq
  have hJ1 : (1:ℝ) ≤ J := by exact_mod_cast ha.trans haJ
  have hf0 : (0:ℝ) ≤ f := Nat.cast_nonneg _
  have hJp : J ≤ p := by
    have : (J:ℝ) ≤ p := by linarith
    exact_mod_cast this
  have hpJ : ((p - J : ℕ):ℝ) = p - J := Nat.cast_sub hJp
  have hp0 : (0:ℝ) < p := by linarith
  have t1 : v ^ (-((f:ℝ) * dN / 2)) ≤ Real.exp ((J:ℝ) * n * f) := by
    have hv0 : 0 < v := by linarith
    rw [Real.rpow_def_of_pos hv0]
    apply Real.exp_le_exp.mpr
    have hlv : 0 ≤ Real.log v + 1 := by
      have h1 : Real.log (1/2) ≤ Real.log v := Real.log_le_log (by norm_num) hv
      have h2 : Real.log (1/2) = - Real.log 2 := by rw [one_div, Real.log_inv]
      have := Real.log_two_lt_d9
      linarith
    have hd : (dN:ℝ) ≤ 2 * J * n := by exact_mod_cast hdN
    have h3 : 0 ≤ (f:ℝ) * dN / 2 := by positivity
    have h4 : (f:ℝ) * dN / 2 ≤ J * n * f := by
      calc (f:ℝ) * dN / 2 ≤ f * (2 * J * n) / 2 := by gcongr
        _ = _ := by ring
    nlinarith [mul_nonneg hlv h3]
  have t2 : C ^ (J * n * f) = Real.exp ((J:ℝ) * n * f * Real.log C) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hC0]; congr 1; push_cast; ring
  have t3 : res ^ a ≤ Real.exp (2 * f * J * (Real.log C + n)) := by
    have hCl : 0 < C * ℓ := by positivity
    calc res ^ a ≤ ((C * ℓ) ^ (2 * f)) ^ a := by gcongr
      _ = Real.exp (((2 * f * a : ℕ):ℝ) * Real.log (C * ℓ)) := by
          rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos hCl, mul_comm]
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          rw [Real.log_mul hC0.ne' hℓ.ne']
          push_cast
          have ha' : (a:ℝ) ≤ J := by exact_mod_cast haJ
          have h0 : 0 ≤ Real.log C + n := by linarith
          calc 2 * (f:ℝ) * a * (Real.log C + Real.log ℓ) ≤ 2 * (f:ℝ) * a * (Real.log C + n) := by
                gcongr
            _ ≤ _ := by gcongr
  have t4 : (C / (p:ℝ)) ^ (J * (p - J))
      ≤ Real.exp (-((J:ℝ) * n / 2 * (Real.log n - 1 - Real.log C))) := by
    have hCp : 0 < C / (p:ℝ) := by positivity
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hCp]
    apply Real.exp_le_exp.mpr
    rw [Real.log_div hC0.ne' hp0.ne', Nat.cast_mul, hpJ]
    have hlp : Real.log n - 1 ≤ Real.log p := by
      have h1 : Real.log (n / 2) ≤ Real.log p := Real.log_le_log (by positivity) (by linarith)
      rw [Real.log_div hn0.ne' (by norm_num)] at h1
      have := Real.log_two_lt_d9; linarith
    have hl : 0 ≤ Real.log n - 1 - Real.log C := by linarith
    have hk : (J:ℝ) * n / 2 ≤ J * (p - J) := by
      have : (n:ℝ) / 2 ≤ p - J := by linarith
      nlinarith
    have hk0 : 0 ≤ (J:ℝ) * (p - J) := le_trans (by positivity) hk
    have a1 : (Real.log C - Real.log p) * ((J:ℝ) * (p - J))
        ≤ (-(Real.log n - 1 - Real.log C)) * ((J:ℝ) * (p - J)) :=
      mul_le_mul_of_nonneg_right (by linarith) hk0
    have a2 := mul_le_mul_of_nonneg_left hk hl
    linarith
  have t5 : (J:ℝ) ^ ((J:ℝ) ^ 2 / 2) ≤ Real.exp ((J:ℝ) * n / 8 * Real.log n) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    have hlJ : Real.log J ≤ Real.log n := Real.log_le_log (by linarith) (by linarith)
    have hlJ0 : 0 ≤ Real.log J := Real.log_nonneg hJ1
    have hJ2 : (J:ℝ) ^ 2 / 2 ≤ J * n / 8 := by nlinarith
    calc Real.log J * ((J:ℝ) ^ 2 / 2) ≤ Real.log n * ((J:ℝ) * n / 8) := by gcongr
      _ = _ := by ring
  have hv0 : 0 < v := by linarith
  calc v ^ (-((f:ℝ) * dN / 2)) * C ^ (J * n * f) * res ^ a
        * ((C / (p:ℝ)) ^ (J * (p - J)) * (J:ℝ) ^ ((J:ℝ) ^ 2 / 2)) ^ f
      ≤ Real.exp ((J:ℝ) * n * f) * Real.exp ((J:ℝ) * n * f * Real.log C)
        * Real.exp (2 * f * J * (Real.log C + n))
        * (Real.exp (-((J:ℝ) * n / 2 * (Real.log n - 1 - Real.log C)))
            * Real.exp ((J:ℝ) * n / 8 * Real.log n)) ^ f := by
        rw [t2]; gcongr
    _ = Real.exp ((J:ℝ) * n * f + (J:ℝ) * n * f * Real.log C + 2 * f * J * (Real.log C + n)
          + f * (-((J:ℝ) * n / 2 * (Real.log n - 1 - Real.log C)) + (J:ℝ) * n / 8 * Real.log n)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hw : 0 ≤ (J:ℝ) * n * f := by positivity
        have h2 : (f:ℝ) * J * Real.log C * 1 ≤ (f:ℝ) * J * Real.log C * n := by
          gcongr; linarith
        have h3 : (J:ℝ) * n * f * (14 * (1 + Real.log C)) ≤ (J:ℝ) * n * f * Real.log n := by gcongr
        linarith

end Formalism.MainNotions.LeviCoordinates
