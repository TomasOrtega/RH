import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostBoundsTwoMulRpowLogSqLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTopCountLeConstMulLog
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (translation)
Introduce `eps he he' C hC`. Use `⟨412, fun cD hcD => ⟨0, fun ch _ => ?_⟩⟩` and prove the remaining obligations. Take `⟨CN, x1, h1⟩` from `GlobalTheory.topCount_and_lambda_bounds eps he he'`. Take `⟨x2, h2⟩` from `GlobalTheory.scale_poly_comparison eps (cD + 12) 1 he one_pos`. Take `⟨x3, h3⟩` from `GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 4) cD 1 (1 / 2) 0 le_rfl (by positivity) (by norm_num)`.

Take `⟨x4, h4⟩` from `GlobalTheory.EX.rank_basic_bounds eps he he'`. Establish `hCp : 1 ≤ C.P.Cpde` using `hC.2.2.2.2.2.2.2.2.2.2.2.2.1`. Take `⟨x5, h5⟩` from `GlobalTheory.EX.hostBounds eps C.P.Cpde he he' hCp`. Establish `hLa : 1 ≤ C.GK.La` using `hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])`. Use `⟨max (max (max x1 x2) (max x3 x4)) (max x5 32), fun D L hε hx hV => ?_⟩` and prove the remaining obligations.

Simplify using `only [max_le_iff] at hx`. Take `⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, hx5, hx6⟩` from `hx`. Establish `hx1' : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hΛ : 1 ≤ L.LaG`.

Rewrite using `[hV.La_eq]`. Use `le_trans ?_ ((h1 L.sc hε hx1).2.2 C.GK hLa).1` and prove the remaining obligations. Conclude with `Real.one_le_rpow hx1'.le L.sc.eps_pos.le`. Establish `hp1 : 1 ≤ L.sc.x ^ cD` using `Real.one_le_rpow hx1'.le (by linarith)`. Establish `hDel : (D.s.Del : ℝ) = (⌈L.sc.x ^ cD⌉₊ : ℝ)`.

Rewrite using `[hV.Del_eq]`. Simplify using `[Delv]`. Establish `hD2 : (D.s.Del : ℝ) ≤ 2 * L.sc.x ^ cD`. Rewrite using `[hDel]`. Use `Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by positivity)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hD0 : L.sc.x ^ cD ≤ (D.s.Del : ℝ)`. Rewrite using `[hDel]`. Conclude with `Nat.le_ceil _`. Establish `hD1 : 1 ≤ (D.s.Del : ℝ)` using `hp1.trans hD0`.

Take `⟨hf, hm, hr, hkr, -, hL, -, -, -, -, -, -, -, -, hN, -, -⟩` from `h4 L.sc D.R hε hx4 hV.ranks`. Take `⟨-, -, -, -, -, hrd1, -, hrd, -, -⟩` from `h5 L.sc D.R D.host hε hx5 hV.ranks hV.host`. Establish `hk0 : (0 : ℝ) < D.R.k` using `lt_of_lt_of_le (by positivity) hV.ranks.2.2.1.1`. Establish `hk : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℕ)`. Establish `: (D.R.k : ℝ) ≤ D.R.r` using `by exact_mod_cast hkr`.

Rewrite using `[← Real.rpow_natCast]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN' : (D.R.N D.R.m : ℝ) ≤ L.sc.x ^ (402 : ℕ)`. Rewrite using `[← Real.rpow_natCast]`.

Use `push_cast`. Conclude with `hN`. Establish `hθ : L.sc.x ^ szTh L ≤ L.sc.x`. Establish `: L.sc.x ^ szTh L ≤ L.sc.x ^ (1 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [szTh, hε]; linarith)`. Rewrite `this` using `[Real.rpow_one]`. Then use the resulting hypothesis.

Establish `hθ0 : 0 < L.sc.x ^ szTh L` using `by positivity`. Establish `hn1 : 1 ≤ D.R.n` using `D.R.ord_pos`. Establish `hn : (D.R.n : ℝ) ≤ L.sc.x ^ (3 : ℝ)`. Use `le_trans ?_ hf` and prove the remaining obligations. Establish `: D.R.n ≤ D.R.f` using `by simp only [Ranks.f]; omega`.

Conclude with `this` after adjusting the coercions. Take `⟨hw, hwb, -⟩` from `(h2 L.sc hε hx2).2.2.2.2.2.1 D.R.n hn1 hn`. Establish `hw' : L.sc.x ^ cD * L.sc.x ^ (12 : ℕ) ≤ L.sc.w'' D.R.n`. Rewrite `hw` using `[sub_self, Real.rpow_zero, one_mul, Real.rpow_add hx0]`. Rewrite using `[← Real.rpow_natCast]`.

Use `push_cast`. Conclude with `hw`. Establish `h412 : L.sc.x ^ (412 : ℕ) ≤ (D.s.Del : ℝ)`. Use `le_trans ?_ hD0` and prove the remaining obligations. Rewrite using `[← Real.rpow_natCast]`.

Conclude with `Real.rpow_le_rpow_of_exponent_le hx1'.le (by push_cast; exact hcD)`. Establish `key : 16 * L.sc.x * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) ≤ L.sc.w'' D.R.n`. Combine the equalities or inequalities in the displayed calculation. Establish `hP : 0 ≤ (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ)` using `by positivity`. Establish `hwΛ : L.sc.w'' D.R.n ≤ L.LaG * L.sc.b'`.

Establish `hb0 : 0 ≤ L.sc.b'` using `le_trans (le_trans (by positivity) hw') hwb`. Conclude with `hwb.trans (le_mul_of_one_le_left hb0 hΛ)`. Establish `hxP : (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) ≤ L.sc.x * ((D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ))` using `le_mul_of_one_le_left hP hx1'.le`. Establish `hθP : L.sc.x ^ szTh L * ((D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ)) ≤ L.sc.x * ((D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ))` using `mul_le_mul_of_nonneg_right hθ hP`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `h` using `h3 L.sc.x hx3`. Simplify using `only [pow_zero, mul_one, Real.rpow_zero] at h`. Establish `h7 : Real.log (D.s.Del : ℝ) ≤ Real.log (2 * L.sc.x ^ cD)` using `Real.log_le_log (by linarith) hD2`.

Rewrite `h7` using `[Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0]`. Establish `h8` using `Real.log_two_lt_d9`. Rewrite using `[hε]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[L.Sc_eq]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmk : (D.R.m : ℝ) ≤ D.R.k`. Use `D.R.m_add_three_le_k` as an intermediate fact. Conclude with `(by omega : D.R.m ≤ D.R.k)` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[le_div_iff₀ hk0, L.Sc_eq]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hv : Real.log D.host.v ≤ L.sc.x`. Use `le_trans ?_ (hrd.trans hL)` and prove the remaining obligations.

Unfold `Host.v`. Conclude with `Real.log_le_log (by linarith) (by linarith)`. Establish `hk3 : L.sc.x ^ (3 : ℕ) ≤ (D.R.k : ℝ)`. Use `le_trans ?_ hV.ranks.2.2.1.1` and prove the remaining obligations. Rewrite using `[← Real.rpow_natCast]`.

Conclude with `Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [hε]; push_cast; linarith)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem szRow_sizeDel : SzRow (fun _ _ L => SizeDel L) := by
  intro eps he he' C hC
  refine ⟨412, fun cD hcD => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨CN, x1, h1⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps (cD + 12) 1 he one_pos
  obtain ⟨x3, h3⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 4) cD 1 (1 / 2) 0 le_rfl
    (by positivity) (by norm_num)
  obtain ⟨x4, h4⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  have hCp : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨x5, h5⟩ := GlobalTheory.EX.hostBounds eps C.P.Cpde he he' hCp
  have hLa : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  refine ⟨max (max (max x1 x2) (max x3 x4)) (max x5 32), fun D L hε hx hV => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, hx5, hx6⟩ := hx
  have hx1' : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hΛ : 1 ≤ L.LaG := by
    rw [hV.La_eq]
    refine le_trans ?_ ((h1 L.sc hε hx1).2.2 C.GK hLa).1
    exact Real.one_le_rpow hx1'.le L.sc.eps_pos.le
  have hp1 : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hx1'.le (by linarith)
  have hDel : (D.s.Del : ℝ) = (⌈L.sc.x ^ cD⌉₊ : ℝ) := by
    rw [hV.Del_eq]; simp [Delv]
  have hD2 : (D.s.Del : ℝ) ≤ 2 * L.sc.x ^ cD := by
    rw [hDel]
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by positivity)
    linarith
  have hD0 : L.sc.x ^ cD ≤ (D.s.Del : ℝ) := by
    rw [hDel]; exact Nat.le_ceil _
  have hD1 : 1 ≤ (D.s.Del : ℝ) := hp1.trans hD0
  obtain ⟨hf, hm, hr, hkr, -, hL, -, -, -, -, -, -, -, -, hN, -, -⟩ := h4 L.sc D.R hε hx4 hV.ranks
  obtain ⟨-, -, -, -, -, hrd1, -, hrd, -, -⟩ := h5 L.sc D.R D.host hε hx5 hV.ranks hV.host
  have hk0 : (0 : ℝ) < D.R.k := lt_of_lt_of_le (by positivity) hV.ranks.2.2.1.1
  have hk : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℕ) := by
    have : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    rw [← Real.rpow_natCast]; push_cast; linarith
  have hN' : (D.R.N D.R.m : ℝ) ≤ L.sc.x ^ (402 : ℕ) := by
    rw [← Real.rpow_natCast]; push_cast; exact hN
  have hθ : L.sc.x ^ szTh L ≤ L.sc.x := by
    have : L.sc.x ^ szTh L ≤ L.sc.x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [szTh, hε]; linarith)
    rwa [Real.rpow_one] at this
  have hθ0 : 0 < L.sc.x ^ szTh L := by positivity
  have hn1 : 1 ≤ D.R.n := D.R.ord_pos
  have hn : (D.R.n : ℝ) ≤ L.sc.x ^ (3 : ℝ) := by
    refine le_trans ?_ hf
    have : D.R.n ≤ D.R.f := by simp only [Ranks.f]; omega
    exact_mod_cast this
  obtain ⟨hw, hwb, -⟩ := (h2 L.sc hε hx2).2.2.2.2.2.1 D.R.n hn1 hn
  have hw' : L.sc.x ^ cD * L.sc.x ^ (12 : ℕ) ≤ L.sc.w'' D.R.n := by
    rw [sub_self, Real.rpow_zero, one_mul, Real.rpow_add hx0] at hw
    rw [← Real.rpow_natCast]; push_cast; exact hw
  have h412 : L.sc.x ^ (412 : ℕ) ≤ (D.s.Del : ℝ) := by
    refine le_trans ?_ hD0
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1'.le (by push_cast; exact hcD)
  have key : 16 * L.sc.x * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) ≤ L.sc.w'' D.R.n := by
    calc 16 * L.sc.x * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ)
        ≤ 16 * L.sc.x * (L.sc.x ^ (5 : ℕ)) ^ 2 * (2 * L.sc.x ^ cD) := by gcongr
      _ = 32 * (L.sc.x ^ cD * L.sc.x ^ (11 : ℕ)) := by ring
      _ ≤ L.sc.x * (L.sc.x ^ cD * L.sc.x ^ (11 : ℕ)) := by gcongr
      _ = L.sc.x ^ cD * L.sc.x ^ (12 : ℕ) := by ring
      _ ≤ _ := hw'
  have hP : 0 ≤ (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) := by positivity
  have hwΛ : L.sc.w'' D.R.n ≤ L.LaG * L.sc.b' := by
    have hb0 : 0 ≤ L.sc.b' := le_trans (le_trans (by positivity) hw') hwb
    exact hwb.trans (le_mul_of_one_le_left hb0 hΛ)
  have hxP : (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) ≤ L.sc.x * ((D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ)) :=
    le_mul_of_one_le_left hP hx1'.le
  have hθP : L.sc.x ^ szTh L * ((D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ)) ≤
      L.sc.x * ((D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ)) := mul_le_mul_of_nonneg_right hθ hP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ L.sc.x ^ (402 : ℕ) * L.sc.x ^ 10 := by gcongr
      _ = L.sc.x ^ (412 : ℕ) := by rw [← pow_add]
      _ ≤ _ := h412
  · calc L.sc.x ^ szTh L * D.R.m * D.R.N D.R.m ≤ L.sc.x * L.sc.x * L.sc.x ^ (402 : ℕ) := by gcongr
      _ = L.sc.x ^ (404 : ℕ) := by ring
      _ ≤ L.sc.x ^ (412 : ℕ) := pow_le_pow_right₀ hx1'.le (by norm_num)
      _ ≤ _ := h412
  · have h := h3 L.sc.x hx3
    simp only [pow_zero, mul_one, Real.rpow_zero] at h
    have h7 : Real.log (D.s.Del : ℝ) ≤ Real.log (2 * L.sc.x ^ cD) := Real.log_le_log (by linarith) hD2
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0] at h7
    have h8 := Real.log_two_lt_d9
    rw [hε]
    linarith
  · rw [L.Sc_eq]
    linarith
  · have hmk : (D.R.m : ℝ) ≤ D.R.k := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (by omega : D.R.m ≤ D.R.k)
    calc L.sc.x ^ szTh L * D.R.m * D.R.k * (D.s.Del : ℝ)
        ≤ L.sc.x ^ szTh L * D.R.k * D.R.k * (D.s.Del : ℝ) := by gcongr
      _ ≤ _ := by linarith
  · rw [le_div_iff₀ hk0, L.Sc_eq]
    linarith
  · linarith
  · have hv : Real.log D.host.v ≤ L.sc.x := by
      refine le_trans ?_ (hrd.trans hL)
      unfold Host.v
      exact Real.log_le_log (by linarith) (by linarith)
    have hk3 : L.sc.x ^ (3 : ℕ) ≤ (D.R.k : ℝ) := by
      refine le_trans ?_ hV.ranks.2.2.1.1
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [hε]; push_cast; linarith)
    calc L.sc.x ^ szTh L * D.R.m * Real.log D.host.v ≤ L.sc.x ^ szTh L * D.R.m * L.sc.x := by gcongr
      _ ≤ L.sc.x * L.sc.x * L.sc.x := by gcongr
      _ = L.sc.x ^ (3 : ℕ) := by ring
      _ ≤ _ := hk3

end GlobalTheory.EX
