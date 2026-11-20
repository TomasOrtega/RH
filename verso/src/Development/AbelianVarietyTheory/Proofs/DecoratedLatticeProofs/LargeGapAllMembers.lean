import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.GapAt

/- English proof (translation)
Establish `hM0 : 0 ≤ M` using `by linarith`. Establish `hk' : 0 ≤ k - 1` using `by linarith`. Establish `hk'' : k - 1 ≤ M` using `by linarith`. Establish `pw : ∀ a b : ℕ, a ≤ b → M ^ a ≤ M ^ b` using `fun a b h => pow_le_pow_right₀ hM h`. Establish `h1 : f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m ≤ M ^ 7`.

Combine the equalities or inequalities in the displayed calculation. Establish `h10 : 0 ≤ f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m`. Establish `: 0 ≤ m` using `by linarith`. Check the signs of the components of the expression. Establish `h2 : n ≤ 28 * M ^ 8`.

Establish `a1 : f ≤ M ^ 7` using `by have := pw 1 7 (by norm_num); rw [pow_one] at this; linarith`. Establish `a2 : r * (f + f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m) ≤ M * (2 * M ^ 7)` using `mul_le_mul hr (by linarith) (by linarith) hM0`. Establish `a3 : M * (2 * M ^ 7) = 2 * M ^ 8` using `by ring`. Establish `a4` using `pw 0 8 (by norm_num)`. Rewrite `a4` using `[pow_zero]`.

Rewrite `hn` using `[mul_assoc]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : t ≤ 40 * M ^ 9`. Establish `a1 : f * r ≤ M * M` using `mul_le_mul hf hr hr0 hM0`. Establish `a2 : T * n ≤ M * (28 * M ^ 8)` using `mul_le_mul hT h2 hn0 hM0`.

Establish `a3 : M * (28 * M ^ 8) = 28 * M ^ 9` using `by ring`. Establish `a4` using `pw 0 9 (by norm_num)`. Establish `a5` using `pw 2 9 (by norm_num)`. Rewrite `a4` using `[pow_zero]`. Rewrite `a5` using `[pow_two]`.

Rewrite `ht` using `[mul_assoc]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : N ≤ 42 * M ^ 10`. Establish `a4` using `pw 0 9 (by norm_num)`. Rewrite `a4` using `[pow_zero]`.

Establish `a1 : m * (t + 1) ≤ M * (41 * M ^ 9)` using `mul_le_mul hm (by linarith) (by linarith) hM0`. Establish `a3 : M * (41 * M ^ 9) = 41 * M ^ 10` using `by ring`. Establish `a5` using `pw 1 10 (by norm_num)`. Rewrite `a5` using `[pow_one]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hN0 : 0 ≤ N`. Rewrite using `[hN]`. Establish `: 0 ≤ m * (t + 1)` using `mul_nonneg (by linarith) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5 : N ^ 3 ≤ 74088 * M ^ 30`.

Combine the equalities or inequalities in the displayed calculation. Establish `a4` using `pw 0 30 (by norm_num)`. Establish `a5` using `pw 9 30 (by norm_num)`. Rewrite `a4` using `[pow_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem poly_bound {M k m f r L T n t N : ℝ} (hM : 1 ≤ M) (hk1 : 1 ≤ k) (hk : k ≤ M) (hm1 : 1 ≤ m) (hm : m ≤ M)
    (hf0 : 0 ≤ f) (hf : f ≤ M) (hr0 : 0 ≤ r) (hr : r ≤ M) (hL0 : 0 ≤ L) (hL : L ≤ M) (hT : T ≤ M) (hn0 : 0 ≤ n)
    (hn : n ≤ 10 * r * (f + f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m) + 8) (ht0 : 0 ≤ t) (ht : t ≤ 8 * f * r + 4 + T * n)
    (hN : N = k + m * (t + 1)) : 4 * N ^ 3 + 2 * t + 6 ≤ 300000 * M ^ 30 := by
  have hM0 : 0 ≤ M := by linarith
  have hk' : 0 ≤ k - 1 := by linarith
  have hk'' : k - 1 ≤ M := by linarith
  have pw : ∀ a b : ℕ, a ≤ b → M ^ a ≤ M ^ b := fun a b h => pow_le_pow_right₀ hM h
  have h1 : f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m ≤ M ^ 7 := by
    calc f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m ≤ f ^ 2 * (k - 1) ^ 3 * L ^ 2 := div_le_self (by positivity) hm1
      _ ≤ M ^ 2 * M ^ 3 * M ^ 2 := by gcongr
      _ = M ^ 7 := by ring
  have h10 : 0 ≤ f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m := by
    have : 0 ≤ m := by linarith
    positivity
  have h2 : n ≤ 28 * M ^ 8 := by
    have a1 : f ≤ M ^ 7 := by have := pw 1 7 (by norm_num); rw [pow_one] at this; linarith
    have a2 : r * (f + f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m) ≤ M * (2 * M ^ 7) :=
      mul_le_mul hr (by linarith) (by linarith) hM0
    have a3 : M * (2 * M ^ 7) = 2 * M ^ 8 := by ring
    have a4 := pw 0 8 (by norm_num)
    rw [pow_zero] at a4
    rw [mul_assoc] at hn
    linarith
  have h3 : t ≤ 40 * M ^ 9 := by
    have a1 : f * r ≤ M * M := mul_le_mul hf hr hr0 hM0
    have a2 : T * n ≤ M * (28 * M ^ 8) := mul_le_mul hT h2 hn0 hM0
    have a3 : M * (28 * M ^ 8) = 28 * M ^ 9 := by ring
    have a4 := pw 0 9 (by norm_num)
    have a5 := pw 2 9 (by norm_num)
    rw [pow_zero] at a4
    rw [pow_two] at a5
    rw [mul_assoc] at ht
    linarith
  have h4 : N ≤ 42 * M ^ 10 := by
    have a4 := pw 0 9 (by norm_num)
    rw [pow_zero] at a4
    have a1 : m * (t + 1) ≤ M * (41 * M ^ 9) := mul_le_mul hm (by linarith) (by linarith) hM0
    have a3 : M * (41 * M ^ 9) = 41 * M ^ 10 := by ring
    have a5 := pw 1 10 (by norm_num)
    rw [pow_one] at a5
    linarith
  have hN0 : 0 ≤ N := by
    rw [hN]
    have : 0 ≤ m * (t + 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  have h5 : N ^ 3 ≤ 74088 * M ^ 30 := by
    calc N ^ 3 ≤ (42 * M ^ 10) ^ 3 := pow_le_pow_left₀ hN0 h4 3
      _ = 74088 * M ^ 30 := by ring
  have a4 := pw 0 30 (by norm_num)
  have a5 := pw 9 30 (by norm_num)
  rw [pow_zero] at a4
  linarith

/- English proof (translation)
Take `⟨-, -, ⟨-, hk⟩, ht⟩` from `h`. Establish `hx` using `s.one_lt_alt.le`. Establish `e0` using `s.eps_pos`. Establish `e1` using `s.eps_lt`. Establish `hY : 1 ≤ s.x ^ (377 : ℝ)` using `Real.one_le_rpow hx (by norm_num)`.

Establish `hk2 : (R.k : ℝ) ≤ 2 * s.x ^ (377 : ℝ)`. Use `Real.rpow_le_rpow_of_exponent_le hx (show 9 / 2 + 10 * s.eps ≤ (377 : ℝ) by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL : s.L ≤ s.x ^ (377 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hx (show s.eps ≤ (377 : ℝ) by linarith)`. Establish `hL0 : 0 ≤ s.L` using `Real.rpow_nonneg (by linarith) _`.

Establish `n1` using `R.two_le_m`. Establish `n2` using `R.m_add_three_le_k`. Establish `hm1 : (1 : ℝ) ≤ R.m` using `by exact_mod_cast (show 1 ≤ R.m by omega)`. Establish `hk1 : (1 : ℝ) ≤ R.k` using `by exact_mod_cast (show 1 ≤ R.k by omega)`. Establish `hmk : (R.m : ℝ) ≤ R.k` using `by exact_mod_cast (show R.m ≤ R.k by omega)`.

Establish `hfk : (R.f : ℝ) ≤ R.k` using `by exact_mod_cast (show R.f ≤ R.k from R.f_le_k)`. Establish `hrk : (R.r : ℝ) ≤ 2 * R.k`. Conclude with `(show R.r ≤ 2 * R.k by unfold Ranks.r; omega)` after adjusting the coercions. Establish `hT : (TOv s : ℝ) ≤ 4 * s.x ^ (377 : ℝ)`. Use `Nat.ceil_lt_add_one (show 0 ≤ s.x ^ (377 : ℝ) by linarith)` as an intermediate fact.

Unfold `TOv`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn : (nWv R s : ℝ) ≤ 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) + 8`. Establish `hk' : (0 : ℝ) ≤ (R.k : ℝ) - 1` using `by linarith`. Use `Nat.ceil_lt_add_one (show 0 ≤ 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8 by positivity)` as an intermediate fact.

Unfold `nWv`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht' : (R.t : ℝ) ≤ 8 * (R.f : ℝ) * R.r + 4 + (TOv s : ℝ) * nWv R s`. Conclude with `(show R.t ≤ 8 * R.f * R.r + 4 + TOv s * nWv R s by omega)` after adjusting the coercions.

Use `poly_bound (by linarith) hk1 (by linarith) hm1 (by linarith) (Nat.cast_nonneg _) (by linarith) (Nat.cast_nonneg _) (by linarith) hL0 (by linarith) hT (Nat.cast_nonneg _) hn (Nat.cast_nonneg _) ht' ?_` and prove the remaining obligations. Unfold `Ranks.N`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem rank_bound (s : Scale) (R : Ranks) (h : RankVal s R) :
    4 * ((R.N R.m : ℕ) : ℝ) ^ 3 + 2 * R.t + 6 ≤ 300000 * (4 * s.x ^ (377 : ℝ)) ^ 30 := by
  obtain ⟨-, -, ⟨-, hk⟩, ht⟩ := h
  have hx := s.one_lt_alt.le
  have e0 := s.eps_pos
  have e1 := s.eps_lt
  have hY : 1 ≤ s.x ^ (377 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hk2 : (R.k : ℝ) ≤ 2 * s.x ^ (377 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hx (show 9 / 2 + 10 * s.eps ≤ (377 : ℝ) by linarith)
    linarith
  have hL : s.L ≤ s.x ^ (377 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (show s.eps ≤ (377 : ℝ) by linarith)
  have hL0 : 0 ≤ s.L := Real.rpow_nonneg (by linarith) _
  have n1 := R.two_le_m
  have n2 := R.m_add_three_le_k
  have hm1 : (1 : ℝ) ≤ R.m := by exact_mod_cast (show 1 ≤ R.m by omega)
  have hk1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (show 1 ≤ R.k by omega)
  have hmk : (R.m : ℝ) ≤ R.k := by exact_mod_cast (show R.m ≤ R.k by omega)
  have hfk : (R.f : ℝ) ≤ R.k := by exact_mod_cast (show R.f ≤ R.k from R.f_le_k)
  have hrk : (R.r : ℝ) ≤ 2 * R.k := by
    exact_mod_cast (show R.r ≤ 2 * R.k by unfold Ranks.r; omega)
  have hT : (TOv s : ℝ) ≤ 4 * s.x ^ (377 : ℝ) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ s.x ^ (377 : ℝ) by linarith)
    unfold TOv
    linarith
  have hn : (nWv R s : ℝ) ≤ 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) + 8 := by
    have hk' : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by linarith
    have := Nat.ceil_lt_add_one
      (show 0 ≤ 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8 by positivity)
    unfold nWv
    push_cast
    linarith
  have ht' : (R.t : ℝ) ≤ 8 * (R.f : ℝ) * R.r + 4 + (TOv s : ℝ) * nWv R s := by
    exact_mod_cast (show R.t ≤ 8 * R.f * R.r + 4 + TOv s * nWv R s by omega)
  refine poly_bound (by linarith) hk1 (by linarith) hm1 (by linarith) (Nat.cast_nonneg _) (by linarith) (Nat.cast_nonneg _)
    (by linarith) hL0 (by linarith) hT (Nat.cast_nonneg _) hn (Nat.cast_nonneg _) ht' ?_
  unfold Ranks.N
  push_cast
  rfl

/- English proof (translation)
Introduce `u τ j hj`. Take `⟨b1, hb, -⟩` from `h.hc.2.2.1`. Rewrite using `[D.hcW_b u τ, (hb τ _).1, (hb τ _).1]`. Use `push_cast`. Conclude with `le_of_eq (by ring)`.
-/
theorem nodeGap_of_val {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (h : Val C cD ch L) : D.NodeGap (h0v L.sc ch : ℝ) := by
  intro u τ j hj
  obtain ⟨b1, hb, -⟩ := h.hc.2.2.1
  rw [D.hcW_b u τ, (hb τ _).1, (hb τ _).1]
  push_cast
  exact le_of_eq (by ring)

/- English proof (translation)
Use `(nodeGap_of_val h).mono ((rank_bound L.sc D.R h.ranks).trans ?_)` and prove the remaining obligations. Establish `h1` using `L.sc.one_lt_alt`. Establish `h0 : 0 < L.sc.x` using `by linarith`. Establish `e1 : (L.sc.x ^ (377 : ℝ)) ^ 30 = L.sc.x ^ (11310 : ℝ)`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul h0.le]`.

Evaluate the numerical expressions. Establish `e2 : L.sc.x * L.sc.x ^ (11310 : ℝ) ≤ L.sc.x ^ ch`. Rewrite using `[mul_comm, ← Real.rpow_add_one h0.ne']`. Conclude with `Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)`. Establish `e3 : 0 ≤ L.sc.x ^ (11310 : ℝ)` using `Real.rpow_nonneg h0.le _`.

Establish `e4` using `mul_le_mul_of_nonneg_right hx e3`. Establish `e5` using `Nat.le_ceil (L.sc.x ^ ch)`. Establish `e6 : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℝ)` using `Nat.cast_nonneg _`. Rewrite using `[mul_pow, e1, ← mul_assoc]`. Unfold `h0v`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bigGap_of_val {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (h : Val C cD ch L) (hch : 11311 ≤ ch)
    (hx : 300000 * 4 ^ 30 ≤ L.sc.x) : BigGap D := by
  refine (nodeGap_of_val h).mono ((rank_bound L.sc D.R h.ranks).trans ?_)
  have h1 := L.sc.one_lt_alt
  have h0 : 0 < L.sc.x := by linarith
  have e1 : (L.sc.x ^ (377 : ℝ)) ^ 30 = L.sc.x ^ (11310 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le]; norm_num
  have e2 : L.sc.x * L.sc.x ^ (11310 : ℝ) ≤ L.sc.x ^ ch := by
    rw [mul_comm, ← Real.rpow_add_one h0.ne']
    exact Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
  have e3 : 0 ≤ L.sc.x ^ (11310 : ℝ) := Real.rpow_nonneg h0.le _
  have e4 := mul_le_mul_of_nonneg_right hx e3
  have e5 := Nat.le_ceil (L.sc.x ^ ch)
  have e6 : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℝ) := Nat.cast_nonneg _
  rw [mul_pow, e1, ← mul_assoc]
  unfold h0v
  push_cast
  linarith

/- English proof (translation)
Introduce `hL p`. Use `⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨11311, fun ch hch _ => ⟨300000 * 4 ^ 30, fun K hK hx β _ _ _ _ => ?_⟩⟩⟩⟩⟩` and prove the remaining obligations. Use `show BigGap β.X.toD7`. Use `bigGap_of_val β.val ?_ ?_` and prove the remaining obligations. Rewrite using `[hK.2.2.1]`.

Conclude with `hch`. Rewrite using `[β.sc]`. Conclude with `hx`.
-/
theorem rowE_bigGap : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => GlobalTheory.Core.Rk.BigGap D) := by
  intro hL p
  refine ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ =>
    ⟨11311, fun ch hch _ => ⟨300000 * 4 ^ 30, fun K hK hx β _ _ _ _ => ?_⟩⟩⟩⟩⟩
  show BigGap β.X.toD7
  refine bigGap_of_val β.val ?_ ?_
  · rw [hK.2.2.1]; exact hch
  · rw [β.sc]; exact hx

end GlobalTheory.Core.Rk.GapAt

end
