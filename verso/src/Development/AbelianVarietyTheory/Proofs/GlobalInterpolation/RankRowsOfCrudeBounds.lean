import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (translation)
Establish `hy0 : 0 < y` using `by linarith`. Establish `hy1 : 1 ≤ y` using `by linarith`. Establish `hpow : ∀ a b : ℕ, a ≤ b → y ^ a ≤ y ^ b` using `fun a b h => pow_le_pow_right₀ hy1 h`. Establish `hk8 : 8 ≤ k`. Use `hpow 1 9 (by norm_num)` as an intermediate fact.

Rewrite `this` using `[pow_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog : 1 ≤ Real.log k`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkk : k ≤ k * Real.log k` using `le_mul_of_one_le_right (by linarith) hlog`. Establish `hff : f ≤ f * Real.log k` using `le_mul_of_one_le_right (le_trans (by positivity) hf) hlog`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rank_rows_of_crude_bounds (y m k f L l A B : ℝ) (hy : 8 ≤ y) (hA : 64 * A ≤ y) (hB : B ≤ y)
    (hm0 : 0 ≤ m) (hm : m ≤ 2 * y) (hk : y ^ 9 ≤ k) (hf : y ^ 4 ≤ f) (hL0 : 0 ≤ L) (hL : L ≤ y)
    (hl0 : 0 ≤ l) (hl : l ≤ y ^ 2) :
    m ^ 2 * L ≤ k ∧ m * y * l ≤ k ∧ A * m ^ 6 * L ≤ k * Real.log k ∧ B * L ≤ f * Real.log k := by
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hpow : ∀ a b : ℕ, a ≤ b → y ^ a ≤ y ^ b := fun a b h => pow_le_pow_right₀ hy1 h
  have hk8 : 8 ≤ k := by
    have := hpow 1 9 (by norm_num)
    rw [pow_one] at this
    linarith
  have hlog : 1 ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hkk : k ≤ k * Real.log k := le_mul_of_one_le_right (by linarith) hlog
  have hff : f ≤ f * Real.log k := le_mul_of_one_le_right (le_trans (by positivity) hf) hlog
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc m ^ 2 * L ≤ (2 * y) ^ 2 * y := by gcongr
      _ = 4 * y ^ 3 := by ring
      _ ≤ y * y ^ 3 := by gcongr; linarith
      _ = y ^ 4 := by ring
      _ ≤ k := (hpow 4 9 (by norm_num)).trans hk
  · calc m * y * l ≤ (2 * y) * y * y ^ 2 := by gcongr
      _ = 2 * y ^ 4 := by ring
      _ ≤ y * y ^ 4 := by gcongr; linarith
      _ = y ^ 5 := by ring
      _ ≤ k := (hpow 5 9 (by norm_num)).trans hk
  · calc A * m ^ 6 * L = A * (m ^ 6 * L) := by ring
      _ ≤ (y / 64) * (m ^ 6 * L) := by gcongr; linarith
      _ ≤ (y / 64) * ((2 * y) ^ 6 * y) := by gcongr
      _ = y ^ 8 := by ring
      _ ≤ k := (hpow 8 9 (by norm_num)).trans hk
      _ ≤ _ := hkk
  · calc B * L ≤ y * L := by gcongr
      _ ≤ y * y := by gcongr
      _ = y ^ 2 := by ring
      _ ≤ f := (hpow 2 4 (by norm_num)).trans hf
      _ ≤ _ := hff

/- English proof (translation)
Introduce `eps he0 he1 C _`. Use `⟨0, fun cD _ => ⟨0, fun ch _ => ⟨(max 8 (max (64 * C.P.Ck6) C.P.CfL)) ^ 2, ?_⟩⟩⟩` and prove the remaining obligations. Introduce `D L _ hx hV`. Take `⟨⟨hn, -⟩, ⟨-, hm⟩, ⟨hk, -⟩, -⟩` from `hV.ranks`. Establish `hx1` using `L.sc.one_lt_alt`.

Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hp` using `L.sc.eps_pos`. Establish `hq` using `L.sc.eps_lt`. Establish `hy : max 8 (max (64 * C.P.Ck6) C.P.CfL) ≤ L.sc.x ^ ((1 : ℝ) / 2)`. Rewrite using `[← Real.sqrt_eq_rpow]`.

Conclude with `Real.le_sqrt_of_sq_le hx`. Establish `hnat : ∀ j : ℕ, (L.sc.x ^ ((1 : ℝ) / 2)) ^ j = L.sc.x ^ ((j : ℝ) / 2)`. Introduce `j`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hx0.le]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hmono : ∀ a b : ℝ, a ≤ b → L.sc.x ^ a ≤ L.sc.x ^ b` using `fun a b h => Real.rpow_le_rpow_of_exponent_le hx1.le h`. Use `rank_rows_of_crude_bounds (L.sc.x ^ ((1 : ℝ) / 2)) _ _ _ _ _ _ _ ((le_max_left _ _).trans hy) (((le_max_left _ _).trans (le_max_right _ _)).trans hy) (((le_max_right _ _).trans (le_max_right _ _)).trans hy) (Nat.cast_nonneg _) ?_ ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Use `hm.trans ?_` and prove the remaining obligations. Rewrite using `[← Real.sqrt_eq_rpow]`.

Establish `hd : L.sc.delta1 ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)`. Establish `: L.sc.x * L.sc.delta1 ≤ L.sc.x` using `mul_le_of_le_one_right hx0.le hd`. Use `gcongr`. Rewrite using `[hnat]`. Conclude with `(hmono _ _ (by push_cast; linarith)).trans hk`.

Rewrite using `[hnat]`. Use `((hmono _ _ (by push_cast; linarith)).trans hn).trans ?_` and prove the remaining obligations. Establish `h0 : (0 : ℝ) ≤ D.R.n` using `Nat.cast_nonneg _`. Unfold `Ranks.f`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `Real.rpow_nonneg hx0.le _`. Conclude with `hmono _ _ (by linarith)`. Conclude with `Real.log_nonneg hx1.le`. Rewrite using `[hnat]`.

Use `Real.log_le_sub_one_of_pos hx0` as an intermediate fact. Evaluate the numerical expressions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem szRow_rank_lower_bounds :
    SzRow (fun C D L => ((D.R.m : ℝ) ^ 2 * L.sc.L ≤ D.R.k) ∧ ((D.R.m : ℝ) * L.sc.x ^ ((1 : ℝ) / 2) * Real.log L.sc.x ≤ D.R.k) ∧ (C.P.Ck6 * (D.R.m : ℝ) ^ 6 * L.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k) ∧ (C.P.CfL * L.sc.L ≤ (D.R.f : ℝ) * Real.log D.R.k)) := by
  intro eps he0 he1 C _
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨(max 8 (max (64 * C.P.Ck6) C.P.CfL)) ^ 2, ?_⟩⟩⟩
  intro D L _ hx hV
  obtain ⟨⟨hn, -⟩, ⟨-, hm⟩, ⟨hk, -⟩, -⟩ := hV.ranks
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hp := L.sc.eps_pos
  have hq := L.sc.eps_lt
  have hy : max 8 (max (64 * C.P.Ck6) C.P.CfL) ≤ L.sc.x ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le hx
  have hnat : ∀ j : ℕ, (L.sc.x ^ ((1 : ℝ) / 2)) ^ j = L.sc.x ^ ((j : ℝ) / 2) := by
    intro j
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  have hmono : ∀ a b : ℝ, a ≤ b → L.sc.x ^ a ≤ L.sc.x ^ b :=
    fun a b h => Real.rpow_le_rpow_of_exponent_le hx1.le h
  refine rank_rows_of_crude_bounds (L.sc.x ^ ((1 : ℝ) / 2)) _ _ _ _ _ _ _
    ((le_max_left _ _).trans hy) (((le_max_left _ _).trans (le_max_right _ _)).trans hy)
    (((le_max_right _ _).trans (le_max_right _ _)).trans hy) (Nat.cast_nonneg _) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine hm.trans ?_
    rw [← Real.sqrt_eq_rpow]
    have hd : L.sc.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)
    have : L.sc.x * L.sc.delta1 ≤ L.sc.x := mul_le_of_le_one_right hx0.le hd
    gcongr
  · rw [hnat]
    exact (hmono _ _ (by push_cast; linarith)).trans hk
  · rw [hnat]
    refine ((hmono _ _ (by push_cast; linarith)).trans hn).trans ?_
    have h0 : (0 : ℝ) ≤ D.R.n := Nat.cast_nonneg _
    unfold Ranks.f
    push_cast
    linarith
  · exact Real.rpow_nonneg hx0.le _
  · exact hmono _ _ (by linarith)
  · exact Real.log_nonneg hx1.le
  · rw [hnat]
    have := Real.log_le_sub_one_of_pos hx0
    norm_num
    linarith

end GlobalTheory.EX
