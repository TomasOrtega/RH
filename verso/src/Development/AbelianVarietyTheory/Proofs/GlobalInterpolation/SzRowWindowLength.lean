import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (translation)
Establish `hx1` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `he0` using `L.sc.eps_pos`. Establish `he1` using `L.sc.eps_lt`. Establish `hk : (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (5 : ℝ)`.

Establish `h1` using `hV.ranks.2.2.1.2`. Establish `h2 : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ L.sc.x ^ (5 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast D.R.two_le_m`. Establish `hn : (0 : ℝ) < D.R.n`.

Establish `: 0 < D.R.n` using `by unfold Ranks.n; positivity`. Conclude with `this` after adjusting the coercions. Establish `hd : L.sc.x ^ (-L.sc.eps) ≤ L.de2`. Rewrite using `[L.typeDensity_eq_card_div, le_div_iff₀ hn]`. Conclude with `hV.host.2.2.1`.

Establish `hd' : L.sc.x ^ (-1 : ℝ) ≤ L.de2` using `le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)) hd`. Establish `hxe : L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (1 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)`. Establish `hdp` using `L.thickDensity_pos`. Unfold `lA`. Rewrite using `[div_le_iff₀ (by positivity)]`.

Establish `e7 : L.sc.x ^ (7 : ℝ) * L.sc.x ^ (-1 : ℝ) = L.sc.x ^ (5 : ℝ) * L.sc.x ^ (1 : ℝ)`. Rewrite using `[← Real.rpow_add hx0, ← Real.rpow_add hx0]`. Evaluate the numerical expressions. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, ← e7]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ L.sc.x ^ (7 : ℝ) * ((D.R.m : ℝ) * L.de2) := by gcongr`.
-/
theorem lA_le_pow_seven {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (hV : Val C cD ch L) :
    lA L ≤ L.sc.x ^ (7 : ℝ) := by
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hk : (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (5 : ℝ) := by
    have h1 := hV.ranks.2.2.1.2
    have h2 : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ L.sc.x ^ (5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    linarith
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hn : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := by unfold Ranks.n; positivity
    exact_mod_cast this
  have hd : L.sc.x ^ (-L.sc.eps) ≤ L.de2 := by
    rw [L.typeDensity_eq_card_div, le_div_iff₀ hn]
    exact hV.host.2.2.1
  have hd' : L.sc.x ^ (-1 : ℝ) ≤ L.de2 :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)) hd
  have hxe : L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hdp := L.thickDensity_pos
  unfold lA
  rw [div_le_iff₀ (by positivity)]
  have e7 : L.sc.x ^ (7 : ℝ) * L.sc.x ^ (-1 : ℝ) = L.sc.x ^ (5 : ℝ) * L.sc.x ^ (1 : ℝ) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num
  calc (D.R.k : ℝ) * L.sc.x ^ L.sc.eps ≤ (2 * L.sc.x ^ (5 : ℝ)) * L.sc.x ^ (1 : ℝ) := by gcongr
    _ = L.sc.x ^ (7 : ℝ) * (2 * L.sc.x ^ (-1 : ℝ)) := by
        rw [mul_assoc, ← e7]; ring
    _ ≤ L.sc.x ^ (7 : ℝ) * ((D.R.m : ℝ) * L.de2) := by gcongr

/- English proof (translation)
Establish `hx1` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `he0` using `L.sc.eps_pos`. Establish `he1` using `L.sc.eps_lt`. Establish `hn : (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (3 : ℝ)`.

Establish `h1` using `hV.ranks.n_le'`. Establish `h2 : L.sc.x ^ ((9 : ℝ) / 4) ≤ L.sc.x ^ (3 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht : (D.R.t : ℝ) ≤ L.sc.x ^ (401 : ℝ)`. Establish `h` using `L.t_win.2`.

Rewrite `h` using `[hV.Ct_eq, hCt]`. Then use the resulting hypothesis. Establish `hm2` using `D.R.two_le_m`. Establish `hm : (0 : ℝ) < D.R.m` using `by exact_mod_cast (by omega : 0 < D.R.m)`. Establish `hN : D.R.N D.R.m ≤ 2 * D.R.t * D.R.m`. Establish `h` using `D.R.rank_add_five_le`.

Establish `h1 : D.R.k + 1 ≤ D.R.t` using `by omega`. Unfold `Ranks.N`. Use the polynomial consequences of the given equalities and inequalities. Establish `hN' : (D.R.N D.R.m : ℝ) ≤ 2 * D.R.t * D.R.m` using `by exact_mod_cast hN`. Rewrite using `[div_le_iff₀ hm]`.

Establish `e : L.sc.x ^ (404 : ℝ) = L.sc.x ^ (3 : ℝ) * L.sc.x ^ (401 : ℝ)`. Rewrite using `[← Real.rpow_add hx0]`. Evaluate the numerical expressions. Combine the equalities or inequalities in the displayed calculation.
-/
theorem nN_div_m_le {C : FC} (hCt : C.Ct = 401) {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (hV : Val C cD ch L) :
    (D.R.n : ℝ) * D.R.N D.R.m / D.R.m ≤ 4 * L.sc.x ^ (404 : ℝ) := by
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hn : (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (3 : ℝ) := by
    have h1 := hV.ranks.n_le'
    have h2 : L.sc.x ^ ((9 : ℝ) / 4) ≤ L.sc.x ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
    linarith
  have ht : (D.R.t : ℝ) ≤ L.sc.x ^ (401 : ℝ) := by
    have h := L.t_win.2
    rwa [hV.Ct_eq, hCt] at h
  have hm2 := D.R.two_le_m
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hN : D.R.N D.R.m ≤ 2 * D.R.t * D.R.m := by
    have h := D.R.rank_add_five_le
    have h1 : D.R.k + 1 ≤ D.R.t := by omega
    unfold Ranks.N
    nlinarith
  have hN' : (D.R.N D.R.m : ℝ) ≤ 2 * D.R.t * D.R.m := by exact_mod_cast hN
  rw [div_le_iff₀ hm]
  have e : L.sc.x ^ (404 : ℝ) = L.sc.x ^ (3 : ℝ) * L.sc.x ^ (401 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  calc (D.R.n : ℝ) * D.R.N D.R.m ≤ (2 * L.sc.x ^ (3 : ℝ)) * (2 * D.R.t * D.R.m) := by gcongr
    _ ≤ (2 * L.sc.x ^ (3 : ℝ)) * (2 * L.sc.x ^ (401 : ℝ) * D.R.m) := by gcongr
    _ = 4 * L.sc.x ^ (404 : ℝ) * D.R.m := by rw [e]; ring

/- English proof (translation)
Introduce `eps h0 h1 C hC`. Use `⟨0, fun cD _ => ⟨0, fun ch _ => ⟨Real.exp (60 / eps + 34), fun D L he hx hV => ?_⟩⟩⟩` and prove the remaining obligations. Establish `hx1` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hlog : 60 / eps + 34 ≤ Real.log L.sc.x` using `(Real.le_log_iff_exp_le hx0).2 hx`.

Establish `hq : 0 < 60 / eps` using `by positivity`. Establish `hLw : D.host.Lw = Lwv L.sc` using `hV.host.2.2.2.2.2.1`. Establish `hCt : C.Ct = 401`. Establish `h` using `hC.1`. Unfold `FC.Fixed at h`.

The claim follows by propositional logic. Use `⟨fun l hl => ⟨⌈7 * Real.log L.sc.x⌉₊, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `hl' : (11 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `he1 : Real.exp 1 ≤ (l : ℝ) - 1`. Use `Real.exp_one_lt_d9` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_one]`. Conclude with `Real.exp_le_exp.2 (Nat.le_ceil _)`. Use `_ = Real.exp 1 ^ ⌈7 * Real.log L.sc.x⌉₊ := Real.exp_nat_mul _ _`.

Use `_ ≤ ((l : ℝ) - 1) ^ ⌈7 * Real.log L.sc.x⌉₊ := by gcongr`. Establish `: ⌈7 * Real.log L.sc.x⌉₊ ≤ ⌈(405 : ℝ) * Real.log L.sc.x⌉₊` using `Nat.ceil_mono (by linarith)`. Rewrite using `[hLw, Lwv]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hLw, hC.2.2.1, Lwv, he]`.

Establish `a1 : (⌈(405 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) < 405 * Real.log L.sc.x + 1` using `Nat.ceil_lt_add_one (by linarith)`. Establish `a2 : (⌈30 / eps⌉₊ : ℝ) < 30 / eps + 1` using `Nat.ceil_lt_add_one (by positivity)`. Establish `a3 : 60 / eps = 2 * (30 / eps)` using `by ring`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hV.logFiveDepth_eq, hC.2.2.2.1]`. Establish `hb` using `nN_div_m_le hCt hV`. Establish `hm2` using `D.R.two_le_m`. Establish `hm : (0 : ℝ) < D.R.m` using `by exact_mod_cast (by omega : 0 < D.R.m)`. Establish `hn : (0 : ℝ) < D.R.n`.

Establish `: 0 < D.R.n` using `by unfold Ranks.n; positivity`. Conclude with `this` after adjusting the coercions. Establish `hN : (0 : ℝ) < D.R.N D.R.m`. Establish `h` using `D.R.m_add_three_le_k`. Establish `: 0 < D.R.N D.R.m` using `by unfold Ranks.N; omega`.

Conclude with `this` after adjusting the coercions. Establish `hy : 0 < (D.R.n : ℝ) * D.R.N D.R.m / D.R.m` using `by positivity`. Establish `l4 : Real.log 4 = 2 * Real.log 2`. Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num`. Establish `l2` using `Real.log_two_gt_d9`.

Establish `l2'` using `Real.log_two_lt_d9`. Establish `l5 : Real.log 4 ≤ Real.log 5` using `Real.log_le_log (by norm_num) (by norm_num)`. Establish `hl : Real.log ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ Real.log 4 + 404 * Real.log L.sc.x`. Use `(Real.log_le_log hy hb).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0]`.

Establish `hlb : Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ 400 * Real.log L.sc.x`. Rewrite using `[Real.logb, div_le_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `a1 : (⌈(400 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) < 400 * Real.log L.sc.x + 1` using `Nat.ceil_lt_add_one (by linarith)`. Establish `a2 : ((⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊ : ℕ) : ℝ) ≤ (⌈(400 : ℝ) * Real.log L.sc.x⌉₊ : ℝ)`.

Conclude with `Nat.ceil_mono hlb` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem szRow_windowLength : SzRow (fun C D L => (∀ l : ℕ, 11 ≤ l → ∃ j : ℕ, lA L ≤ ((l : ℝ) - 1) ^ j ∧ 2 * j + 2 ≤ D.host.Lw) ∧ ((D.host.Lw : ℝ) ≤ C.P.CLw * Real.log L.sc.x) ∧ ((L.j0 : ℝ) ≤ C.P.Cj0 * Real.log L.sc.x)) := by
  intro eps h0 h1 C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨Real.exp (60 / eps + 34), fun D L he hx hV => ?_⟩⟩⟩
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hlog : 60 / eps + 34 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hx0).2 hx
  have hq : 0 < 60 / eps := by positivity
  have hLw : D.host.Lw = Lwv L.sc := hV.host.2.2.2.2.2.1
  have hCt : C.Ct = 401 := by
    have h := hC.1
    unfold FC.Fixed at h
    tauto
  refine ⟨fun l hl => ⟨⌈7 * Real.log L.sc.x⌉₊, ?_, ?_⟩, ?_, ?_⟩
  · have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
    have he1 : Real.exp 1 ≤ (l : ℝ) - 1 := by
      have := Real.exp_one_lt_d9
      linarith
    calc lA L ≤ L.sc.x ^ (7 : ℝ) := lA_le_pow_seven hV
      _ = Real.exp (7 * Real.log L.sc.x) := by rw [Real.rpow_def_of_pos hx0, mul_comm]
      _ ≤ Real.exp ((⌈7 * Real.log L.sc.x⌉₊ : ℕ) * 1) := by
          rw [mul_one]; exact Real.exp_le_exp.2 (Nat.le_ceil _)
      _ = Real.exp 1 ^ ⌈7 * Real.log L.sc.x⌉₊ := Real.exp_nat_mul _ _
      _ ≤ ((l : ℝ) - 1) ^ ⌈7 * Real.log L.sc.x⌉₊ := by gcongr
  · have : ⌈7 * Real.log L.sc.x⌉₊ ≤ ⌈(405 : ℝ) * Real.log L.sc.x⌉₊ := Nat.ceil_mono (by linarith)
    rw [hLw, Lwv]; omega
  · rw [hLw, hC.2.2.1, Lwv, he]
    have a1 : (⌈(405 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) < 405 * Real.log L.sc.x + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    have a2 : (⌈30 / eps⌉₊ : ℝ) < 30 / eps + 1 := Nat.ceil_lt_add_one (by positivity)
    have a3 : 60 / eps = 2 * (30 / eps) := by ring
    push_cast
    linarith
  · rw [hV.logFiveDepth_eq, hC.2.2.2.1]
    have hb := nN_div_m_le hCt hV
    have hm2 := D.R.two_le_m
    have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
    have hn : (0 : ℝ) < D.R.n := by
      have : 0 < D.R.n := by unfold Ranks.n; positivity
      exact_mod_cast this
    have hN : (0 : ℝ) < D.R.N D.R.m := by
      have h := D.R.m_add_three_le_k
      have : 0 < D.R.N D.R.m := by unfold Ranks.N; omega
      exact_mod_cast this
    have hy : 0 < (D.R.n : ℝ) * D.R.N D.R.m / D.R.m := by positivity
    have l4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have l2 := Real.log_two_gt_d9
    have l2' := Real.log_two_lt_d9
    have l5 : Real.log 4 ≤ Real.log 5 := Real.log_le_log (by norm_num) (by norm_num)
    have hl : Real.log ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ Real.log 4 + 404 * Real.log L.sc.x := by
      refine (Real.log_le_log hy hb).trans (le_of_eq ?_)
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0]
    have hlb : Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ 400 * Real.log L.sc.x := by
      rw [Real.logb, div_le_iff₀ (by linarith)]
      nlinarith
    have a1 : (⌈(400 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) < 400 * Real.log L.sc.x + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    have a2 : ((⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊ : ℕ) : ℝ) ≤ (⌈(400 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) := by
      exact_mod_cast Nat.ceil_mono hlb
    linarith

end GlobalTheory.EX
