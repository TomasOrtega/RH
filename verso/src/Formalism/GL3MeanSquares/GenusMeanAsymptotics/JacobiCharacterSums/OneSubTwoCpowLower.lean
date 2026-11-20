import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensLs
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZMoll
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDetect

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

/- English proof (translation)
Rewrite using `[Subsingleton.elim x 1, map_one]`.
-/
lemma one_char_apply (x : ZMod 1) : (1 : DirichletCharacter ℂ 1) x = 1 := by
  rw [Subsingleton.elim x 1, map_one]

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hsplit : ∑ n ∈ Ioc Y (Y * N'), mco Y N' n * f n * (n : ℂ) ^ (-ρ) = ∑ j ∈ range J', blkD Y N' (Y * 2 ^ j) f ρ`. Establish `h0` using `sum_blocks (fun n => mco Y N' n * f n * (n : ℂ) ^ (-ρ)) Y J'`. Rewrite `h0` using `[← hN]`.

Conclude with `h0`. Establish `hJpos : (0 : ℝ) < J'` using `by exact_mod_cast hJ`. Establish `hlt : ‖∑ n ∈ Ioc Y (Y * N'), mco Y N' n * f n * (n : ℂ) ^ (-ρ)‖ < θ`. Rewrite using `[hsplit]`. Use `(norm_sum_le _ _).trans_lt ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma block_pigeon (Y J' N' : ℕ) (f : ℕ → ℂ) (ρ : ℂ) (hN : N' = 2 ^ J') (hJ : 0 < J') (θ : ℝ)
    (h : θ ≤ ‖∑ n ∈ Ioc Y (Y * N'), mco Y N' n * f n * (n : ℂ) ^ (-ρ)‖) :
    ∃ j ∈ range J', θ / (J' : ℝ) ≤ ‖blkD Y N' (Y * 2 ^ j) f ρ‖ := by
  by_contra hcon
  push Not at hcon
  have hsplit : ∑ n ∈ Ioc Y (Y * N'), mco Y N' n * f n * (n : ℂ) ^ (-ρ) =
      ∑ j ∈ range J', blkD Y N' (Y * 2 ^ j) f ρ := by
    have h0 := sum_blocks (fun n => mco Y N' n * f n * (n : ℂ) ^ (-ρ)) Y J'
    rw [← hN] at h0
    exact h0
  have hJpos : (0 : ℝ) < J' := by exact_mod_cast hJ
  have hlt : ‖∑ n ∈ Ioc Y (Y * N'), mco Y N' n * f n * (n : ℂ) ^ (-ρ)‖ < θ := by
    rw [hsplit]
    refine (norm_sum_le _ _).trans_lt ?_
    calc ∑ j ∈ range J', ‖blkD Y N' (Y * 2 ^ j) f ρ‖
        < ∑ j ∈ range J', θ / (J' : ℝ) := sum_lt_sum_of_nonempty (nonempty_range_iff.mpr hJ.ne') hcon
      _ = θ := by rw [sum_const, card_range, nsmul_eq_mul]; field_simp
  linarith

/- English proof (translation)
Establish `h` using `Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (1 - ρ)`. Simplify using `using h`.
-/
lemma two_cpow_norm (ρ : ℂ) : ‖(2 : ℂ) ^ (1 - ρ)‖ = (2 : ℝ) ^ (1 - ρ.re) := by
  have h := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (1 - ρ)
  simpa using h

/- English proof (translation)
Establish `h1 : ‖(2 : ℂ) ^ (1 - ρ)‖ - ‖(1 : ℂ)‖ ≤ ‖(2 : ℂ) ^ (1 - ρ) - 1‖` using `norm_sub_norm_le _ _`. Rewrite `h1` using `[norm_sub_rev, two_cpow_norm, norm_one]`. Establish `h2 : Real.log 2 * (1 - ρ.re) + 1 ≤ (2 : ℝ) ^ (1 - ρ.re)`. Rewrite using `[Real.rpow_def_of_pos (by norm_num)]`. Conclude with `Real.add_one_le_exp _`.

Establish `h3 : (1 / 2 : ℝ) ≤ Real.log 2`. Use `Real.log_two_gt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : (1 / 2 : ℝ) * (1 - ρ.re) ≤ Real.log 2 * (1 - ρ.re)` using `mul_le_mul_of_nonneg_right h3 (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma one_sub_two_cpow_lower (ρ : ℂ) (hρ : ρ.re ≤ 1) : (1 - ρ.re) / 2 ≤ ‖1 - (2 : ℂ) ^ (1 - ρ)‖ := by
  have h1 : ‖(2 : ℂ) ^ (1 - ρ)‖ - ‖(1 : ℂ)‖ ≤ ‖(2 : ℂ) ^ (1 - ρ) - 1‖ := norm_sub_norm_le _ _
  rw [norm_sub_rev, two_cpow_norm, norm_one] at h1
  have h2 : Real.log 2 * (1 - ρ.re) + 1 ≤ (2 : ℝ) ^ (1 - ρ.re) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    exact Real.add_one_le_exp _
  have h3 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h4 : (1 / 2 : ℝ) * (1 - ρ.re) ≤ Real.log 2 * (1 - ρ.re) :=
    mul_le_mul_of_nonneg_right h3 (by linarith)
  linarith

/- English proof (translation)
Rewrite using `[two_cpow_norm]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma two_cpow_norm_le (ρ : ℂ) (hρ : 0 ≤ ρ.re) : ‖(2 : ℂ) ^ (1 - ρ)‖ ≤ 2 := by
  rw [two_cpow_norm]
  calc (2 : ℝ) ^ (1 - ρ.re) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 2 := Real.rpow_one 2

attribute [local irreducible] qd pYd pJd pNd in
/- English proof (translation)
Take `⟨c₀, hc₀, hZ⟩` from `zFRDirichlet`. Use `⟨c₀ / 24, by positivity, ⌈96 / c₀⌉₊, ?_⟩` and prove the remaining obligations. Introduce `M _ T hT hM hq ρ hρ hρim hL`. Take `⟨X, hX⟩ : ∃ X : ℕ, qd M T = X` from `⟨_, rfl⟩`. Rewrite `hq`, the goal using `[hX]`.

Establish `hMT : (M : ℝ) * T ≤ X` using `by rw [← hX]; unfold qd; exact Nat.le_ceil _`. Establish `hM3 : (3 : ℝ) ≤ M` using `by exact_mod_cast hM`. Establish `hX6 : (6 : ℝ) ≤ X` using `by nlinarith`. Establish `hXpos : (0 : ℝ) < X` using `by linarith`. Establish `hX1 : 1 ≤ X` using `by exact_mod_cast (show (1 : ℝ) ≤ X by linarith)`.

Establish `hTX : T ≤ X` using `by nlinarith`. Establish `hre0 : 0 < ρ.re` using `by linarith`. Establish `hNX : X ^ 8 ≤ pNd M T`. Establish `h` using `Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X`. Unfold `pNd pJd`.

Rewrite using `[hX, mul_comm 8, pow_mul]`. Conclude with `Nat.pow_le_pow_left h.le 8`. Establish `hY : pYd M T = X ^ 3` using `by unfold pYd; rw [hX]`. Establish `hYN : pYd M T ≤ pNd M T`. Rewrite using `[hY]; exact le_trans (Nat.pow_le_pow_right hX1 (by norm_num)) hNX`.

Establish `hY1 : 1 ≤ pYd M T` using `by rw [hY]; exact Nat.one_le_pow _ _ (by omega)`. Establish `hN1 : 1 ≤ pNd M T` using `le_trans hY1 hYN`. Establish `hJ8 : 8 ≤ pJd M T` using `by unfold pJd; omega`. Establish `hlogX : 0 < Real.log X` using `Real.log_pos (by linarith)`. Establish `hnot : ¬ InRegion c₀ M ρ` using `fun h => (hZ M 1 ρ h hL).2.1 rfl`.

Unfold `InRegion at hnot`. Use `push Not at hnot`. Establish `harg1 : (1 : ℝ) < (M : ℝ) * (|ρ.im| + 2)`. Use `abs_nonneg ρ.im` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `harg2 : (M : ℝ) * (|ρ.im| + 2) ≤ (X : ℝ) ^ 2`. Establish `h1 : (M : ℝ) * (|ρ.im| + 2) ≤ (M : ℝ) * (T + 2)` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hlog2 : Real.log ((M : ℝ) * (|ρ.im| + 2)) ≤ 2 * Real.log X`. Establish `h` using `Real.log_le_log (by linarith) harg2`.

Rewrite `h` using `[Real.log_pow, Nat.cast_ofNat]`. Then use the resulting hypothesis. Establish `hbeta : c₀ / (2 * Real.log X) < 1 - ρ.re`. Establish `h1 : c₀ / (2 * Real.log X) ≤ c₀ / Real.log ((M : ℝ) * (|ρ.im| + 2))` using `div_le_div_of_nonneg_left hc₀.le (Real.log_pos harg1) hlog2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbeta0 : ρ.re ≤ 1`.

Establish `: 0 < c₀ / (2 * Real.log X)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hζ` using `principal_zeta_bound M ρ hre0 hL`. Establish `hρ1 : ρ ≠ 1` using `hL.1.resolve_left (fun h => h rfl)`. Establish `hE` using `eta_partial_sums ρ hre0 hρ1 (pNd M T) hN1`.

Rewrite `hE` using `[hζ, mul_zero, zero_sub, norm_neg]`. Establish `hP : ∀ K : ℕ, ∑ n ∈ Icc 1 K, (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * (n : ℂ) ^ (-ρ) = ∑ n ∈ Icc 1 K, (n : ℂ) ^ (-ρ)` using `fun K => sum_congr rfl (fun n _ => by rw [one_char_apply, one_mul])`. Establish `hMI1` using `mollifier_identity 1 (1 : DirichletCharacter ℂ 1) ρ (pYd M T) (pNd M T) (pYd M T * pNd M T) hY1 hYN le_rfl`. Establish `hMI2` using `mollifier_identity 1 (1 : DirichletCharacter ℂ 1) ρ (pYd M T) (2 * pNd M T) (pYd M T * (2 * pNd M T)) hY1 (by omega) le_rfl`. Rewrite `hMI1`, `hMI2` using `[hP]`.

Establish `hMo` using `mollM_norm_le (1 : DirichletCharacter ℂ 1) ρ hre0.le (pYd M T)`. Establish `hz2` using `two_cpow_norm_le ρ hre0.le`. Establish `hzl` using `one_sub_two_cpow_lower ρ hbeta0`. Use `set z : ℂ := (2 : ℂ) ^ (1 - ρ) with hz`. Use `set P1 := ∑ n ∈ Icc 1 (pNd M T), (n : ℂ) ^ (-ρ) with hP1`.

Use `set P2 := ∑ n ∈ Icc 1 (2 * pNd M T), (n : ℂ) ^ (-ρ) with hP2`. Use `set Mo := ∑ d ∈ Icc 1 (pYd M T), (((ArithmeticFunction.moebius d : ℤ)) : ℂ) * (1 : DirichletCharacter ℂ 1) (d : ZMod 1) * (d : ℂ) ^ (-ρ) with hMdef`. Use `set D1 := ∑ n ∈ Ioc (pYd M T) (pYd M T * pNd M T), mco (pYd M T) (pNd M T) n * (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * (n : ℂ) ^ (-ρ) with hD1`. Use `set D2 := ∑ n ∈ Ioc (pYd M T) (pYd M T * (2 * pNd M T)), mco (pYd M T) (2 * pNd M T) n * (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * (n : ℂ) ^ (-ρ) with hD2`. Establish `hEY : ‖P2 - z * P1‖ * (pYd M T : ℝ) ≤ 12 / (X : ℝ) ^ 2`.

Establish `hNpos : (0 : ℝ) < pNd M T` using `by exact_mod_cast hN1`. Establish `hrho : 1 + ‖ρ‖ / ρ.re ≤ 3 * T`. Establish `h1 : ‖ρ‖ ≤ ρ.re + T`. Use `(Complex.norm_le_abs_re_add_abs_im ρ).trans ?_` and prove the remaining obligations. Rewrite using `[abs_of_pos hre0]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : ‖ρ‖ / ρ.re ≤ 1 + T / ρ.re`. Rewrite using `[div_le_iff₀ hre0, add_mul, one_mul, div_mul_cancel₀ _ hre0.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : T / ρ.re ≤ 4 / 3 * T`.

Rewrite using `[div_le_iff₀ hre0]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpow : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ))` using `Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)`. Establish `hN8 : (X : ℝ) ^ (8 : ℕ) ≤ (pNd M T : ℝ)` using `by exact_mod_cast hNX`.

Establish `hpow2 : (X : ℝ) ^ (6 : ℕ) ≤ ((pNd M T : ℕ) : ℝ) ^ (3 / 4 : ℝ)`. Establish `e : ((X : ℝ) ^ (8 : ℕ)) ^ (3 / 4 : ℝ) = (X : ℝ) ^ (6 : ℕ)`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hXpos.le, ← Real.rpow_natCast]`. Evaluate the numerical expressions. Rewrite using `[← e]`.

Conclude with `Real.rpow_le_rpow (by positivity) hN8 (by norm_num)`. Establish `hinv : ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 / (X : ℝ) ^ (6 : ℕ)`. Rewrite using `[Real.rpow_neg hNpos.le, one_div]`. Conclude with `inv_anti₀ (by positivity) hpow2`. Establish `hYr : (pYd M T : ℝ) = (X : ℝ) ^ (3 : ℕ)` using `by rw [hY, Nat.cast_pow]`.

Establish `hc : 4 * (1 + ‖ρ‖ / ρ.re) ≤ 12 * X` using `by linarith`. Establish `hPle : ‖P2 - z * P1‖ ≤ 12 * X * (1 / (X : ℝ) ^ (6 : ℕ))`. Use `hE.trans ?_` and prove the remaining obligations. Establish `a3 : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ 1 / (X : ℝ) ^ (6 : ℕ)` using `hpow.trans hinv`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hYr]`. Combine the equalities or inequalities in the displayed calculation. Establish `hX0 : (X : ℝ) ≠ 0` using `hXpos.ne'`. Clear the denominators using the available nonvanishing facts. Establish `hsmall : 12 / (X : ℝ) ^ 2 ≤ c₀ / (8 * Real.log X)`.

Establish `h96 : 96 ≤ (X : ℝ) * c₀`. Establish `h` using `Nat.ceil_le.mp hq`. Rewrite `h` using `[div_le_iff₀ hc₀]`. Then use the resulting hypothesis. Establish `hl : Real.log X ≤ X` using `(Real.log_le_sub_one_of_pos hXpos).trans (by linarith)`. Rewrite using `[div_le_div_iff₀ (by positivity) (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hkey : 1 - z = (P2 - z * P1) * Mo - D2 + z * D1`. Take the linear combination `(-1 : ℂ) * hMI2 + z * hMI1`. Establish `hnorm : ‖1 - z‖ ≤ 12 / (X : ℝ) ^ 2 + ‖D2‖ + 2 * ‖D1‖`. Rewrite using `[hkey]`.

Combine the equalities or inequalities in the displayed calculation. Use `norm_sub_le ((P2 - z * P1) * Mo) D2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ ≤ 12 / (X : ℝ) ^ 2 + ‖D2‖ + 2 * ‖D1‖ := by`. Rewrite using `[norm_mul, norm_mul]`.

Establish `a1 : ‖P2 - z * P1‖ * ‖Mo‖ ≤ ‖P2 - z * P1‖ * (pYd M T : ℝ)` using `mul_le_mul_of_nonneg_left hMo (norm_nonneg _)`. Establish `a2 : ‖z‖ * ‖D1‖ ≤ 2 * ‖D1‖` using `mul_le_mul_of_nonneg_right hz2 (norm_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set θ : ℝ := c₀ / (24 * Real.log X) with hθ`. Establish `hθ0 : 0 < θ` using `by positivity`.

Establish `hsum : 3 * θ < ‖D2‖ + 2 * ‖D1‖`. Establish `e1 : c₀ / (2 * Real.log X) / 2 = 6 * θ` using `by rw [hθ]; field_simp; norm_num`. Establish `e2 : c₀ / (8 * Real.log X) = 3 * θ` using `by rw [hθ]; field_simp; norm_num`. Establish `: c₀ / (2 * Real.log X) / 2 < (1 - ρ.re) / 2` using `by linarith`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hJpos : (0 : ℝ) < pJd M T` using `by exact_mod_cast (by omega : 0 < pJd M T)`. Establish `hgoal : c₀ / 24 / (((pJd M T : ℝ) + 1) * Real.log X) = θ / ((pJd M T : ℝ) + 1)`. Rewrite using `[hθ]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hgoal]`.

Distinguish the cases in `hc2 : θ ≤ ‖D2‖`. Take `⟨j, hj, hjb⟩` from `block_pigeon (pYd M T) (pJd M T + 1) (2 * pNd M T) (fun n => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) ρ (by unfold pNd; rw [pow_succ]; ring) (by omega) θ hc2`. Use `⟨1, by simp, j, hj, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one]`. Move the coercions through the operations in `at hjb`.

Conclude with `hjb`. Establish `hc1 : θ ≤ ‖D1‖` using `by push Not at hc2`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨j, hj, hjb⟩` from `block_pigeon (pYd M T) (pJd M T) (pNd M T) (fun n => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) ρ (by unfold pNd; rfl) (by omega) θ hc1`. Use `⟨0, by simp, j, ?_, ?_⟩` and prove the remaining obligations.

Rewrite `hj`, the goal using `[mem_range]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[pow_zero, one_mul]`. Use `le_trans ?_ hjb` and prove the remaining obligations. Conclude with `div_le_div_of_nonneg_left hθ0.le hJpos (by linarith)`.
-/
theorem zero_detection_first : Detect0 := by
  obtain ⟨c₀, hc₀, hZ⟩ := zFRDirichlet
  refine ⟨c₀ / 24, by positivity, ⌈96 / c₀⌉₊, ?_⟩
  intro M _ T hT hM hq ρ hρ hρim hL
  obtain ⟨X, hX⟩ : ∃ X : ℕ, qd M T = X := ⟨_, rfl⟩
  rw [hX] at hq ⊢
  have hMT : (M : ℝ) * T ≤ X := by rw [← hX]; unfold qd; exact Nat.le_ceil _
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hX6 : (6 : ℝ) ≤ X := by nlinarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hX1 : 1 ≤ X := by exact_mod_cast (show (1 : ℝ) ≤ X by linarith)
  have hTX : T ≤ X := by nlinarith
  have hre0 : 0 < ρ.re := by linarith
  have hNX : X ^ 8 ≤ pNd M T := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    unfold pNd pJd
    rw [hX, mul_comm 8, pow_mul]
    exact Nat.pow_le_pow_left h.le 8
  have hY : pYd M T = X ^ 3 := by unfold pYd; rw [hX]
  have hYN : pYd M T ≤ pNd M T := by
    rw [hY]; exact le_trans (Nat.pow_le_pow_right hX1 (by norm_num)) hNX
  have hY1 : 1 ≤ pYd M T := by rw [hY]; exact Nat.one_le_pow _ _ (by omega)
  have hN1 : 1 ≤ pNd M T := le_trans hY1 hYN
  have hJ8 : 8 ≤ pJd M T := by unfold pJd; omega
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)

  have hnot : ¬ InRegion c₀ M ρ := fun h => (hZ M 1 ρ h hL).2.1 rfl
  unfold InRegion at hnot
  push Not at hnot
  have harg1 : (1 : ℝ) < (M : ℝ) * (|ρ.im| + 2) := by
    have := abs_nonneg ρ.im
    nlinarith
  have harg2 : (M : ℝ) * (|ρ.im| + 2) ≤ (X : ℝ) ^ 2 := by
    have h1 : (M : ℝ) * (|ρ.im| + 2) ≤ (M : ℝ) * (T + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  have hlog2 : Real.log ((M : ℝ) * (|ρ.im| + 2)) ≤ 2 * Real.log X := by
    have h := Real.log_le_log (by linarith) harg2
    rwa [Real.log_pow, Nat.cast_ofNat] at h
  have hbeta : c₀ / (2 * Real.log X) < 1 - ρ.re := by
    have h1 : c₀ / (2 * Real.log X) ≤ c₀ / Real.log ((M : ℝ) * (|ρ.im| + 2)) :=
      div_le_div_of_nonneg_left hc₀.le (Real.log_pos harg1) hlog2
    linarith
  have hbeta0 : ρ.re ≤ 1 := by
    have : 0 < c₀ / (2 * Real.log X) := by positivity
    linarith

  have hζ := principal_zeta_bound M ρ hre0 hL
  have hρ1 : ρ ≠ 1 := hL.1.resolve_left (fun h => h rfl)
  have hE := eta_partial_sums ρ hre0 hρ1 (pNd M T) hN1
  rw [hζ, mul_zero, zero_sub, norm_neg] at hE

  have hP : ∀ K : ℕ, ∑ n ∈ Icc 1 K, (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * (n : ℂ) ^ (-ρ) =
      ∑ n ∈ Icc 1 K, (n : ℂ) ^ (-ρ) :=
    fun K => sum_congr rfl (fun n _ => by rw [one_char_apply, one_mul])
  have hMI1 := mollifier_identity 1 (1 : DirichletCharacter ℂ 1) ρ (pYd M T) (pNd M T) (pYd M T * pNd M T)
    hY1 hYN le_rfl
  have hMI2 := mollifier_identity 1 (1 : DirichletCharacter ℂ 1) ρ (pYd M T) (2 * pNd M T)
    (pYd M T * (2 * pNd M T)) hY1 (by omega) le_rfl
  rw [hP] at hMI1 hMI2
  have hMo := mollM_norm_le (1 : DirichletCharacter ℂ 1) ρ hre0.le (pYd M T)
  have hz2 := two_cpow_norm_le ρ hre0.le
  have hzl := one_sub_two_cpow_lower ρ hbeta0
  set z : ℂ := (2 : ℂ) ^ (1 - ρ) with hz
  set P1 := ∑ n ∈ Icc 1 (pNd M T), (n : ℂ) ^ (-ρ) with hP1
  set P2 := ∑ n ∈ Icc 1 (2 * pNd M T), (n : ℂ) ^ (-ρ) with hP2
  set Mo := ∑ d ∈ Icc 1 (pYd M T), (((ArithmeticFunction.moebius d : ℤ)) : ℂ) *
    (1 : DirichletCharacter ℂ 1) (d : ZMod 1) * (d : ℂ) ^ (-ρ) with hMdef
  set D1 := ∑ n ∈ Ioc (pYd M T) (pYd M T * pNd M T), mco (pYd M T) (pNd M T) n *
    (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * (n : ℂ) ^ (-ρ) with hD1
  set D2 := ∑ n ∈ Ioc (pYd M T) (pYd M T * (2 * pNd M T)), mco (pYd M T) (2 * pNd M T) n *
    (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * (n : ℂ) ^ (-ρ) with hD2
  have hEY : ‖P2 - z * P1‖ * (pYd M T : ℝ) ≤ 12 / (X : ℝ) ^ 2 := by
    have hNpos : (0 : ℝ) < pNd M T := by exact_mod_cast hN1
    have hrho : 1 + ‖ρ‖ / ρ.re ≤ 3 * T := by
      have h1 : ‖ρ‖ ≤ ρ.re + T := by
        refine (Complex.norm_le_abs_re_add_abs_im ρ).trans ?_
        rw [abs_of_pos hre0]; linarith
      have h2 : ‖ρ‖ / ρ.re ≤ 1 + T / ρ.re := by
        rw [div_le_iff₀ hre0, add_mul, one_mul, div_mul_cancel₀ _ hre0.ne']; linarith
      have h3 : T / ρ.re ≤ 4 / 3 * T := by
        rw [div_le_iff₀ hre0]; nlinarith
      linarith
    have hpow : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
    have hN8 : (X : ℝ) ^ (8 : ℕ) ≤ (pNd M T : ℝ) := by exact_mod_cast hNX
    have hpow2 : (X : ℝ) ^ (6 : ℕ) ≤ ((pNd M T : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
      have e : ((X : ℝ) ^ (8 : ℕ)) ^ (3 / 4 : ℝ) = (X : ℝ) ^ (6 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le, ← Real.rpow_natCast]
        norm_num
      rw [← e]
      exact Real.rpow_le_rpow (by positivity) hN8 (by norm_num)
    have hinv : ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 / (X : ℝ) ^ (6 : ℕ) := by
      rw [Real.rpow_neg hNpos.le, one_div]
      exact inv_anti₀ (by positivity) hpow2
    have hYr : (pYd M T : ℝ) = (X : ℝ) ^ (3 : ℕ) := by rw [hY, Nat.cast_pow]
    have hc : 4 * (1 + ‖ρ‖ / ρ.re) ≤ 12 * X := by linarith
    have hPle : ‖P2 - z * P1‖ ≤ 12 * X * (1 / (X : ℝ) ^ (6 : ℕ)) := by
      refine hE.trans ?_
      have a3 : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ 1 / (X : ℝ) ^ (6 : ℕ) := hpow.trans hinv
      calc 4 * (1 + ‖ρ‖ / ρ.re) * ((pNd M T : ℕ) : ℝ) ^ (-ρ.re)
          ≤ 12 * X * ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) :=
            mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ 12 * X * (1 / (X : ℝ) ^ (6 : ℕ)) := mul_le_mul_of_nonneg_left a3 (by positivity)
    rw [hYr]
    calc ‖P2 - z * P1‖ * (X : ℝ) ^ (3 : ℕ) ≤ 12 * X * (1 / (X : ℝ) ^ (6 : ℕ)) * (X : ℝ) ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_right hPle (by positivity)
      _ = 12 / (X : ℝ) ^ 2 := by
          have hX0 : (X : ℝ) ≠ 0 := hXpos.ne'
          field_simp
  have hsmall : 12 / (X : ℝ) ^ 2 ≤ c₀ / (8 * Real.log X) := by
    have h96 : 96 ≤ (X : ℝ) * c₀ := by
      have h := Nat.ceil_le.mp hq
      rwa [div_le_iff₀ hc₀] at h
    have hl : Real.log X ≤ X := (Real.log_le_sub_one_of_pos hXpos).trans (by linarith)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hkey : 1 - z = (P2 - z * P1) * Mo - D2 + z * D1 := by
    linear_combination (-1 : ℂ) * hMI2 + z * hMI1
  have hnorm : ‖1 - z‖ ≤ 12 / (X : ℝ) ^ 2 + ‖D2‖ + 2 * ‖D1‖ := by
    rw [hkey]
    calc ‖(P2 - z * P1) * Mo - D2 + z * D1‖ ≤ ‖(P2 - z * P1) * Mo - D2‖ + ‖z * D1‖ := norm_add_le _ _
      _ ≤ ‖(P2 - z * P1) * Mo‖ + ‖D2‖ + ‖z * D1‖ := by
          have := norm_sub_le ((P2 - z * P1) * Mo) D2
          linarith
      _ ≤ 12 / (X : ℝ) ^ 2 + ‖D2‖ + 2 * ‖D1‖ := by
          rw [norm_mul, norm_mul]
          have a1 : ‖P2 - z * P1‖ * ‖Mo‖ ≤ ‖P2 - z * P1‖ * (pYd M T : ℝ) :=
            mul_le_mul_of_nonneg_left hMo (norm_nonneg _)
          have a2 : ‖z‖ * ‖D1‖ ≤ 2 * ‖D1‖ := mul_le_mul_of_nonneg_right hz2 (norm_nonneg _)
          linarith
  set θ : ℝ := c₀ / (24 * Real.log X) with hθ
  have hθ0 : 0 < θ := by positivity
  have hsum : 3 * θ < ‖D2‖ + 2 * ‖D1‖ := by
    have e1 : c₀ / (2 * Real.log X) / 2 = 6 * θ := by rw [hθ]; field_simp; norm_num
    have e2 : c₀ / (8 * Real.log X) = 3 * θ := by rw [hθ]; field_simp; norm_num
    have : c₀ / (2 * Real.log X) / 2 < (1 - ρ.re) / 2 := by linarith
    linarith
  have hJpos : (0 : ℝ) < pJd M T := by exact_mod_cast (by omega : 0 < pJd M T)
  have hgoal : c₀ / 24 / (((pJd M T : ℝ) + 1) * Real.log X) = θ / ((pJd M T : ℝ) + 1) := by
    rw [hθ]; field_simp
  rw [hgoal]
  by_cases hc2 : θ ≤ ‖D2‖
  · obtain ⟨j, hj, hjb⟩ := block_pigeon (pYd M T) (pJd M T + 1) (2 * pNd M T)
      (fun n => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) ρ
      (by unfold pNd; rw [pow_succ]; ring) (by omega) θ hc2
    refine ⟨1, by simp, j, hj, ?_⟩
    rw [pow_one]
    push_cast at hjb
    exact hjb
  · have hc1 : θ ≤ ‖D1‖ := by
      push Not at hc2
      linarith
    obtain ⟨j, hj, hjb⟩ := block_pigeon (pYd M T) (pJd M T) (pNd M T)
      (fun n => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) ρ
      (by unfold pNd; rfl) (by omega) θ hc1
    refine ⟨0, by simp, j, ?_, ?_⟩
    · rw [mem_range] at hj ⊢; omega
    rw [pow_zero, one_mul]
    refine le_trans ?_ hjb
    exact div_le_div_of_nonneg_left hθ0.le hJpos (by linarith)

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
