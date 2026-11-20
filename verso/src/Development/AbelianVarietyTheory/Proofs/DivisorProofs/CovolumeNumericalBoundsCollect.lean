import Mathlib
open Real

namespace GlobalTheory

/- English proof (translation)
Introduce `CG CB f r Lb S N0 sz c₁ q ℓ lb dd hCG hCB hf hr hLb hS hq hqr hℓ hℓL hc hN0 hN0u hsz hszu hlb hdd`. Establish `hfr : 1 ≤ f * r` using `by nlinarith`. Establish `hfrF : f * r ≤ f * r * Lb` using `by nlinarith`. Establish `hrLbF : r * Lb ≤ f * r * Lb` using `by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r) (by linarith : (0:ℝ) ≤ Lb)]`. Establish `hrF : r ≤ f * r * Lb` using `by nlinarith`.

Take `⟨F, hFd⟩ : ∃ F, F = f * r * Lb` from `⟨_, rfl⟩`. Rewrite `hlb`, `hdd`, `hfrF`, `hrLbF`, `hrF`, the goal using `[← hFd]`. Establish `hF : 1 ≤ F` using `by linarith`. Establish `hF2 : F ^ 2 ≤ F ^ 5` using `pow_le_pow_right₀ hF (by norm_num)`. Establish `hF3 : F ^ 3 ≤ F ^ 5` using `pow_le_pow_right₀ hF (by norm_num)`.

Establish `hF4 : F ^ 4 ≤ F ^ 5` using `pow_le_pow_right₀ hF (by norm_num)`. Establish `hF1 : F ≤ F ^ 3` using `by simpa using pow_le_pow_right₀ hF (by norm_num : 1 ≤ 3)`. Establish `hY : 1 ≤ F ^ 5` using `one_le_pow₀ hF`. Establish `hX : 0 ≤ F ^ 3 * S` using `mul_nonneg (by positivity) hS`. Establish `hlog : Real.log (2 * π) ≤ 7`.

Use `Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 2 * π)` as an intermediate fact. Use `Real.pi_le_four` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfrsq : (f * r) ^ 2 ≤ F ^ 2`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 hfrF) (by linarith : (0:ℝ) ≤ F + f * r)]`.

Establish `hT1a : (f * r + 1) * (2 * (f * r) * Real.log (2 * π)) ≤ (f * r + 1) * (2 * (f * r) * 7)` using `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by linarith)) (by linarith)`. Establish `hT1 : (f * r + 1) * (2 * (f * r) * Real.log (2 * π)) ≤ 28 * F ^ 5` using `by nlinarith`. Establish `hql : q * ℓ ≤ r * (3 * Lb)` using `mul_le_mul hqr hℓL hℓ (by linarith)`. Establish `hA : |c₁| + q * ℓ ≤ 12 * (r * Lb)` using `by linarith`. Establish `hffr : f ≤ f * (f * r)` using `by nlinarith`.

Establish `hB : N0 ≤ S + 9 * (f * (f * r))`. Establish `e : f * (4 * (f * r + 1) + 1) = 4 * (f * (f * r)) + 5 * f` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hAB : (|c₁| + q * ℓ) * N0 ≤ 12 * (r * Lb) * (S + 9 * (f * (f * r)))` using `mul_le_mul hA hB hN0 (by positivity)`. Establish `hrLbS : r * Lb * S ≤ F ^ 3 * S` using `mul_le_mul_of_nonneg_right (by linarith) hS`.

Establish `hFfr : r * Lb * (f * (f * r)) ≤ F ^ 5`. Establish `e : r * Lb * (f * (f * r)) = F * (f * r)` using `by rw [hFd]; ring`. Rewrite using `[e]`. Establish `: F * (f * r) ≤ F * F` using `mul_le_mul_of_nonneg_left hfrF (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hT2 : (|c₁| + q * ℓ) * N0 ≤ 12 * (F ^ 3 * S) + 108 * F ^ 5`. Establish `e : 12 * (r * Lb) * (S + 9 * (f * (f * r))) = 12 * (r * Lb * S) + 108 * (r * Lb * (f * (f * r)))` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsz1 : (1 + r) * S ≤ 2 * F * S` using `mul_le_mul_of_nonneg_right (by linarith) hS`. Establish `hsz2 : r * f * (4 * (f * r + 1) + 1) ≤ 9 * F ^ 2`.

Establish `e : r * f * (4 * (f * r + 1) + 1) = 4 * (f * r) ^ 2 + 5 * (f * r)` using `by ring`. Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hsz' : sz ≤ 2 * F * S + 9 * F ^ 2` using `by linarith`. Establish `hT6a : CG * F ^ 2 * sz ≤ CG * F ^ 2 * (2 * F * S + 9 * F ^ 2)` using `mul_le_mul_of_nonneg_left hsz' (by positivity)`.

Establish `hT6b : CG * F ^ 4 ≤ CG * F ^ 5` using `mul_le_mul_of_nonneg_left hF4 hCG`. Establish `hT6 : CG * F ^ 2 * sz ≤ 2 * (CG * (F ^ 3 * S)) + 9 * (CG * F ^ 5)`. Establish `e : CG * F ^ 2 * (2 * F * S + 9 * F ^ 2) = 2 * (CG * (F ^ 3 * S)) + 9 * (CG * F ^ 4)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlb' : lb ≤ CB * F ^ 5` using `le_trans hlb (mul_le_mul_of_nonneg_left hF2 hCB)`.

Establish `hdd' : dd ≤ 196 * F ^ 5` using `by linarith`. Establish `p1 : 0 ≤ CG * (F ^ 3 * S)` using `mul_nonneg hCG hX`. Establish `p2 : 0 ≤ CB * (F ^ 3 * S)` using `mul_nonneg hCB hX`. Establish `p3 : 0 ≤ CG * F ^ 5` using `mul_nonneg hCG (by positivity)`. Establish `e : (11 * CG + CB + 500) * (F ^ 3 * S + F ^ 5) = 11 * (CG * (F ^ 3 * S)) + CB * (F ^ 3 * S) + 500 * (F ^ 3 * S) + 11 * (CG * F ^ 5) + CB * F ^ 5 + 500 * F ^ 5` using `by ring`.

Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem covol_numerical_collect : ∀ (CG CB f r Lb S N0 sz c₁ q ℓ lb dd : ℝ), 0 ≤ CG → 0 ≤ CB → 1 ≤ f → 1 ≤ r → 1 ≤ Lb → 0 ≤ S → 0 ≤ q → q ≤ r → 0 ≤ ℓ → ℓ ≤ 3 * Lb → |c₁| ≤ 9 * r * Lb → 0 ≤ N0 → N0 ≤ S + f * (4 * (f * r + 1) + 1) → 0 ≤ sz → sz ≤ (1 + r) * S + r * f * (4 * (f * r + 1) + 1) → lb ≤ CB * (f * r * Lb) ^ 2 → dd ≤ 391 / 2 * (f * r * Lb) ^ 2 → (f * r + 1) * (2 * (f * r) * Real.log (2 * Real.pi)) + ((|c₁| + q * ℓ) * N0 + lb + dd + 1) + CG * (f * r * Lb) ^ 2 * sz ≤ (11 * CG + CB + 500) * ((f * r * Lb) ^ 3 * S + (f * r * Lb) ^ 5) := by
  intro CG CB f r Lb S N0 sz c₁ q ℓ lb dd hCG hCB hf hr hLb hS hq hqr hℓ hℓL hc hN0 hN0u hsz hszu hlb hdd
  have hfr : 1 ≤ f * r := by nlinarith
  have hfrF : f * r ≤ f * r * Lb := by nlinarith
  have hrLbF : r * Lb ≤ f * r * Lb := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r) (by linarith : (0:ℝ) ≤ Lb)]
  have hrF : r ≤ f * r * Lb := by nlinarith
  obtain ⟨F, hFd⟩ : ∃ F, F = f * r * Lb := ⟨_, rfl⟩
  rw [← hFd] at hlb hdd hfrF hrLbF hrF ⊢
  have hF : 1 ≤ F := by linarith
  have hF2 : F ^ 2 ≤ F ^ 5 := pow_le_pow_right₀ hF (by norm_num)
  have hF3 : F ^ 3 ≤ F ^ 5 := pow_le_pow_right₀ hF (by norm_num)
  have hF4 : F ^ 4 ≤ F ^ 5 := pow_le_pow_right₀ hF (by norm_num)
  have hF1 : F ≤ F ^ 3 := by simpa using pow_le_pow_right₀ hF (by norm_num : 1 ≤ 3)
  have hY : 1 ≤ F ^ 5 := one_le_pow₀ hF
  have hX : 0 ≤ F ^ 3 * S := mul_nonneg (by positivity) hS

  have hlog : Real.log (2 * π) ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 2 * π)
    have := Real.pi_le_four
    linarith
  have hfrsq : (f * r) ^ 2 ≤ F ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hfrF) (by linarith : (0:ℝ) ≤ F + f * r)]
  have hT1a : (f * r + 1) * (2 * (f * r) * Real.log (2 * π)) ≤ (f * r + 1) * (2 * (f * r) * 7) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by linarith)) (by linarith)
  have hT1 : (f * r + 1) * (2 * (f * r) * Real.log (2 * π)) ≤ 28 * F ^ 5 := by nlinarith

  have hql : q * ℓ ≤ r * (3 * Lb) := mul_le_mul hqr hℓL hℓ (by linarith)
  have hA : |c₁| + q * ℓ ≤ 12 * (r * Lb) := by linarith
  have hffr : f ≤ f * (f * r) := by nlinarith
  have hB : N0 ≤ S + 9 * (f * (f * r)) := by
    have e : f * (4 * (f * r + 1) + 1) = 4 * (f * (f * r)) + 5 * f := by ring
    linarith
  have hAB : (|c₁| + q * ℓ) * N0 ≤ 12 * (r * Lb) * (S + 9 * (f * (f * r))) :=
    mul_le_mul hA hB hN0 (by positivity)
  have hrLbS : r * Lb * S ≤ F ^ 3 * S := mul_le_mul_of_nonneg_right (by linarith) hS
  have hFfr : r * Lb * (f * (f * r)) ≤ F ^ 5 := by
    have e : r * Lb * (f * (f * r)) = F * (f * r) := by rw [hFd]; ring
    rw [e]
    have : F * (f * r) ≤ F * F := mul_le_mul_of_nonneg_left hfrF (by linarith)
    nlinarith
  have hT2 : (|c₁| + q * ℓ) * N0 ≤ 12 * (F ^ 3 * S) + 108 * F ^ 5 := by
    have e : 12 * (r * Lb) * (S + 9 * (f * (f * r))) = 12 * (r * Lb * S) + 108 * (r * Lb * (f * (f * r))) := by ring
    linarith

  have hsz1 : (1 + r) * S ≤ 2 * F * S := mul_le_mul_of_nonneg_right (by linarith) hS
  have hsz2 : r * f * (4 * (f * r + 1) + 1) ≤ 9 * F ^ 2 := by
    have e : r * f * (4 * (f * r + 1) + 1) = 4 * (f * r) ^ 2 + 5 * (f * r) := by ring
    rw [e]; nlinarith
  have hsz' : sz ≤ 2 * F * S + 9 * F ^ 2 := by linarith
  have hT6a : CG * F ^ 2 * sz ≤ CG * F ^ 2 * (2 * F * S + 9 * F ^ 2) :=
    mul_le_mul_of_nonneg_left hsz' (by positivity)
  have hT6b : CG * F ^ 4 ≤ CG * F ^ 5 := mul_le_mul_of_nonneg_left hF4 hCG
  have hT6 : CG * F ^ 2 * sz ≤ 2 * (CG * (F ^ 3 * S)) + 9 * (CG * F ^ 5) := by
    have e : CG * F ^ 2 * (2 * F * S + 9 * F ^ 2) = 2 * (CG * (F ^ 3 * S)) + 9 * (CG * F ^ 4) := by ring
    linarith
  have hlb' : lb ≤ CB * F ^ 5 := le_trans hlb (mul_le_mul_of_nonneg_left hF2 hCB)
  have hdd' : dd ≤ 196 * F ^ 5 := by linarith
  have p1 : 0 ≤ CG * (F ^ 3 * S) := mul_nonneg hCG hX
  have p2 : 0 ≤ CB * (F ^ 3 * S) := mul_nonneg hCB hX
  have p3 : 0 ≤ CG * F ^ 5 := mul_nonneg hCG (by positivity)
  have e : (11 * CG + CB + 500) * (F ^ 3 * S + F ^ 5)
      = 11 * (CG * (F ^ 3 * S)) + CB * (F ^ 3 * S) + 500 * (F ^ 3 * S) + 11 * (CG * F ^ 5) + CB * F ^ 5 + 500 * F ^ 5 := by ring
  rw [e]
  linarith

end GlobalTheory
