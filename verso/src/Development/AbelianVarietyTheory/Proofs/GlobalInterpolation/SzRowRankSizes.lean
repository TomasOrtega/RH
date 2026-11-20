import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (translation)
Introduce `eps h0 h1 C hC`. Use `⟨0, fun cD _ => ⟨0, fun ch _ => ⟨Real.exp (100 / eps * (2 * C.P.Cpde) + 4455), fun D L he hx hV => ?_⟩⟩⟩` and prove the remaining obligations. Establish `hx1` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hlog' : 100 / eps * (2 * C.P.Cpde) + 4455 ≤ Real.log L.sc.x` using `(Real.le_log_iff_exp_le hx0).2 hx`.

Establish `hq : 0 < 100 / eps` using `by positivity`. Establish `hC1 : 1 ≤ C.P.Cpde` using `hV.host.one_le`. Establish `hlog : 100 / eps + 4455 ≤ Real.log L.sc.x`. Use `mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * C.P.Cpde by linarith) hq.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hth : szTh L = eps / 100` using `by rw [szTh, he]`. Establish `hth0 : 0 ≤ szTh L` using `by rw [hth]; positivity`. Establish `h2C : 2 * C.P.Cpde ≤ L.sc.x ^ szTh L`. Rewrite using `[Real.rpow_def_of_pos hx0, hth]`. Establish `a : 2 * C.P.Cpde ≤ Real.log L.sc.x * (eps / 100)`.

Establish `b : 100 / eps * (2 * C.P.Cpde) * (eps / 100) = 2 * C.P.Cpde` using `by field_simp`. Establish `c : 100 / eps * (2 * C.P.Cpde) * (eps / 100) ≤ Real.log L.sc.x * (eps / 100)` using `mul_le_mul_of_nonneg_right (by linarith) (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Real.add_one_le_exp (Real.log L.sc.x * (eps / 100))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h2 : 2 ≤ L.sc.x ^ szTh L` using `by linarith`. Establish `hneg : L.sc.x ^ (-szTh L) ≤ 1 / 2`. Rewrite using `[Real.rpow_neg hx0.le, ← one_div]`. Conclude with `one_div_le_one_div_of_le (by norm_num) h2`. Establish `hlo : ∀ a : ℝ, L.sc.x ^ (a - szTh L) ≤ L.sc.x ^ a` using `fun a => Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)`.

Establish `hhi : ∀ a : ℝ, 2 * L.sc.x ^ a ≤ L.sc.x ^ (a + szTh L)` using `fun a => by`. Rewrite using `[Real.rpow_add hx0, mul_comm]`. Conclude with `mul_le_mul_of_nonneg_left h2 (by positivity)`. Establish `hn : (0 : ℝ) < D.R.n`. Establish `: 0 < D.R.n` using `by unfold Ranks.n; positivity`.

Conclude with `this` after adjusting the coercions. Establish `n2 : (D.R.n : ℝ) ≤ L.sc.x ^ (2 + 8 * L.sc.eps + szTh L)`. Use `(hV.ranks.n_le_of_o hV.host.o_le).trans ?_` and prove the remaining obligations. Rewrite using `[Real.rpow_add hx0 (2 + 8 * L.sc.eps), mul_comm]`. Conclude with `mul_le_mul_of_nonneg_left h2C (by positivity)`.

Take `⟨⟨n1, -⟩, ⟨m1, m2⟩, ⟨k1, k2⟩, -⟩` from `hV.ranks`. Take `⟨-, ⟨t1, t2⟩, d2, -, -, hLw, -⟩` from `hV.host`. Establish `hs` using `Real.sqrt_nonneg (L.sc.x * L.sc.delta1)`. Establish `hd1 : 0 ≤ L.sc.delta1` using `by unfold Scale.delta1; positivity`. Use `⟨⟨(hlo _).trans n1, n2⟩, ⟨?_, ?_⟩, ⟨(hlo _).trans k1, k2.trans (hhi _)⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Use `mul_le_mul_of_nonneg_right hneg hs` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `m2.trans (mul_le_mul_of_nonneg_right h2 hs)`. Establish `h` using `D.R.rank_add_five_le`. Conclude with `(by omega : 1 ≤ D.R.t)` after adjusting the coercions.

Conclude with `L.t_win.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith))`. Use `mul_le_mul_of_nonneg_right hneg (mul_nonneg hn.le hd1)` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Conclude with `t2.trans (le_of_eq (by unfold szNst; ring))`. Unfold `SizeDe2`.

Rewrite using `[L.typeDensity_eq_card_div, le_div_iff₀ hn]`. Conclude with `d2`. Unfold `SizeLw`. Rewrite using `[hLw, Lwv, he]`. Establish `a1 : (⌈(405 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) < 405 * Real.log L.sc.x + 1` using `Nat.ceil_lt_add_one (by linarith)`.

Establish `a2 : (⌈30 / eps⌉₊ : ℝ) < 30 / eps + 1` using `Nat.ceil_lt_add_one (by positivity)`. Establish `a3 : 100 / eps = 10 / 3 * (30 / eps)` using `by ring`. Establish `a4 : 4455 * Real.log L.sc.x ≤ Real.log L.sc.x ^ 2` using `by nlinarith`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem szRow_rankSizes : SzRow (fun _ _ L => SizeN L ∧ SizeM L ∧ SizeK L ∧ SizeT L ∧ SizeTT L ∧ SizeDe2 L ∧ SizeLw L) := by
  intro eps h0 h1 C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨Real.exp (100 / eps * (2 * C.P.Cpde) + 4455), fun D L he hx hV => ?_⟩⟩⟩
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hlog' : 100 / eps * (2 * C.P.Cpde) + 4455 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hx0).2 hx
  have hq : 0 < 100 / eps := by positivity
  have hC1 : 1 ≤ C.P.Cpde := hV.host.one_le
  have hlog : 100 / eps + 4455 ≤ Real.log L.sc.x := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * C.P.Cpde by linarith) hq.le
    linarith
  have hth : szTh L = eps / 100 := by rw [szTh, he]
  have hth0 : 0 ≤ szTh L := by rw [hth]; positivity
  have h2C : 2 * C.P.Cpde ≤ L.sc.x ^ szTh L := by
    rw [Real.rpow_def_of_pos hx0, hth]
    have a : 2 * C.P.Cpde ≤ Real.log L.sc.x * (eps / 100) := by
      have b : 100 / eps * (2 * C.P.Cpde) * (eps / 100) = 2 * C.P.Cpde := by field_simp
      have c : 100 / eps * (2 * C.P.Cpde) * (eps / 100) ≤ Real.log L.sc.x * (eps / 100) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    have := Real.add_one_le_exp (Real.log L.sc.x * (eps / 100))
    linarith
  have h2 : 2 ≤ L.sc.x ^ szTh L := by linarith
  have hneg : L.sc.x ^ (-szTh L) ≤ 1 / 2 := by
    rw [Real.rpow_neg hx0.le, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hlo : ∀ a : ℝ, L.sc.x ^ (a - szTh L) ≤ L.sc.x ^ a := fun a =>
    Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hhi : ∀ a : ℝ, 2 * L.sc.x ^ a ≤ L.sc.x ^ (a + szTh L) := fun a => by
    rw [Real.rpow_add hx0, mul_comm]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hn : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := by unfold Ranks.n; positivity
    exact_mod_cast this
  have n2 : (D.R.n : ℝ) ≤ L.sc.x ^ (2 + 8 * L.sc.eps + szTh L) := by
    refine (hV.ranks.n_le_of_o hV.host.o_le).trans ?_
    rw [Real.rpow_add hx0 (2 + 8 * L.sc.eps), mul_comm]
    exact mul_le_mul_of_nonneg_left h2C (by positivity)
  obtain ⟨⟨n1, -⟩, ⟨m1, m2⟩, ⟨k1, k2⟩, -⟩ := hV.ranks
  obtain ⟨-, ⟨t1, t2⟩, d2, -, -, hLw, -⟩ := hV.host
  have hs := Real.sqrt_nonneg (L.sc.x * L.sc.delta1)
  have hd1 : 0 ≤ L.sc.delta1 := by unfold Scale.delta1; positivity
  refine ⟨⟨(hlo _).trans n1, n2⟩, ⟨?_, ?_⟩, ⟨(hlo _).trans k1, k2.trans (hhi _)⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right hneg hs
    linarith
  · exact m2.trans (mul_le_mul_of_nonneg_right h2 hs)
  · have h := D.R.rank_add_five_le
    exact_mod_cast (by omega : 1 ≤ D.R.t)
  · exact L.t_win.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith))
  · have := mul_le_mul_of_nonneg_right hneg (mul_nonneg hn.le hd1)
    calc L.sc.x ^ (-szTh L) * D.R.n * L.sc.delta1 = L.sc.x ^ (-szTh L) * (D.R.n * L.sc.delta1) := by ring
      _ ≤ 1 / 2 * (D.R.n * L.sc.delta1) := this
      _ = L.sc.delta1 * D.R.n / 2 := by ring
      _ ≤ _ := t1
  · exact t2.trans (le_of_eq (by unfold szNst; ring))
  · unfold SizeDe2
    rw [L.typeDensity_eq_card_div, le_div_iff₀ hn]
    exact d2
  · unfold SizeLw
    rw [hLw, Lwv, he]
    have a1 : (⌈(405 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) < 405 * Real.log L.sc.x + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    have a2 : (⌈30 / eps⌉₊ : ℝ) < 30 / eps + 1 := Nat.ceil_lt_add_one (by positivity)
    have a3 : 100 / eps = 10 / 3 * (30 / eps) := by ring
    have a4 : 4455 * Real.log L.sc.x ≤ Real.log L.sc.x ^ 2 := by nlinarith
    push_cast
    linarith

end GlobalTheory.EX
