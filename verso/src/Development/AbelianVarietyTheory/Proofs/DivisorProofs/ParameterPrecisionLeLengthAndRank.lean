import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.LogQdLeRd
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToNatFloorCast

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.CovTop.WtShape

/- English proof (translation)
Establish `h1 : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE` using `(UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1`. Establish `hq' : (2 : ℝ) ≤ D.host.q` using `by exact_mod_cast hq`. Establish `hd' : (2 : ℝ) ≤ D.host.d` using `by exact_mod_cast hd`. Establish `h4 : (2 : ℝ) ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d)`. Rewrite using `[Real.le_sqrt' (by norm_num)]; nlinarith`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem two_le_rdE (D : D7) (hq : 2 ≤ D.host.q) (hd : 2 ≤ D.host.d) : 2 ≤ D.host.rdE := by
  have h1 : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
    (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1
  have hq' : (2 : ℝ) ≤ D.host.q := by exact_mod_cast hq
  have hd' : (2 : ℝ) ≤ D.host.d := by exact_mod_cast hd
  have h4 : (2 : ℝ) ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d) := by
    rw [Real.le_sqrt' (by norm_num)]; nlinarith
  linarith

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Establish `h1 : n = 0 ∨ n = 1` using `by omega`. Apply the tactic sequence `rcases h1 with rfl | rfl <;> simp at h`.
-/
theorem two_le_of_log_pos (n : ℕ) (h : 0 < Real.log (n : ℝ)) : 2 ≤ n := by
  by_contra hn
  have h1 : n = 0 ∨ n = 1 := by omega
  rcases h1 with rfl | rfl <;> simp at h

/- English proof (translation)
Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hL1 : 1 ≤ L.sc.L` using `by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le`. Establish `hq2 : 2 ≤ D.host.q` using `two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.1)`. Establish `hd2 : 2 ≤ D.host.d` using `two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.2.2.2.1)`.

Establish `hq' : (2 : ℝ) ≤ D.host.q` using `by exact_mod_cast hq2`. Establish `hd' : (2 : ℝ) ≤ D.host.d` using `by exact_mod_cast hd2`. Establish `hrd2` using `two_le_rdE D hq2 hd2`. Establish `hn1 : (1 : ℝ) ≤ D.R.n`. Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`.

Conclude with `this` after adjusting the coercions. Establish `ht1 : (1 : ℝ) ≤ D.R.t`. Establish `: 1 ≤ D.R.t` using `by have := D.R.rank_add_five_le; omega`. Conclude with `this` after adjusting the coercions. Establish `hb1 : 1 ≤ L.sc.b` using `by unfold Scale.b; exact Real.one_le_exp (by linarith)`.

Establish `hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d` using `by nlinarith`. Establish `hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d` using `Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩`. Establish `hc : D.host.rdE ≤ Formalism.MainNotions.szCond L`. Use `hQD.2.2.2.2.2.2.2.trans ?_` and prove the remaining obligations. Unfold `Formalism.MainNotions.szCond`.

Establish `h0 : (0 : ℝ) ≤ D.host.QS` using `Nat.cast_nonneg _`. Establish `: (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.QS * ((D.host.q : ℝ) * D.host.d)` using `mul_le_mul_of_nonneg_left hs h0`. Use polynomial arithmetic with `[mul_nonneg h0 (Real.sqrt_nonneg ((D.host.q : ℝ) * D.host.d))]`. Establish `hc1 : 1 ≤ Formalism.MainNotions.szCond L` using `by linarith`. Establish `h36 : Formalism.MainNotions.szCond L ≤ Formalism.MainNotions.szCond L ^ 36` using `le_self_pow₀ hc1 (by norm_num)`.

Establish `h150 : Formalism.MainNotions.szCond L ^ 36 ≤ Formalism.MainNotions.szCond L ^ 36 * (D.R.t : ℝ) ^ 150` using `le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1)`. Establish `hsb : Real.sqrt L.sc.b ≤ L.sc.b` using `Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩`. Establish `hfin : D.host.rdE ≤ L.sc.b` using `hc.trans (h36.trans (h150.trans (hCond.trans hsb)))`. Use `Real.log_le_log (by linarith) hfin` as an intermediate fact. Rewrite `this` using `[show Real.log L.sc.b = L.sc.L by unfold Scale.b; exact Real.log_exp _]`. Then use the resulting hypothesis.
-/
theorem log_rdE_le_L (D : D7) (L : SizeData₂ D) (hCond : Formalism.MainNotions.SizeCond L) (hQD : Formalism.MainNotions.SizeQD L) :
    Real.log D.host.rdE ≤ L.sc.L := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hq2 : 2 ≤ D.host.q := two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.1)
  have hd2 : 2 ≤ D.host.d := two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.2.2.2.1)
  have hq' : (2 : ℝ) ≤ D.host.q := by exact_mod_cast hq2
  have hd' : (2 : ℝ) ≤ D.host.d := by exact_mod_cast hd2
  have hrd2 := two_le_rdE D hq2 hd2
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have ht1 : (1 : ℝ) ≤ D.R.t := by
    have : 1 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
    exact_mod_cast this
  have hb1 : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp (by linarith)
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hc : D.host.rdE ≤ Formalism.MainNotions.szCond L := by
    refine hQD.2.2.2.2.2.2.2.trans ?_
    unfold Formalism.MainNotions.szCond
    have h0 : (0 : ℝ) ≤ D.host.QS := Nat.cast_nonneg _
    have : (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.QS * ((D.host.q : ℝ) * D.host.d) :=
      mul_le_mul_of_nonneg_left hs h0
    nlinarith [mul_nonneg h0 (Real.sqrt_nonneg ((D.host.q : ℝ) * D.host.d))]
  have hc1 : 1 ≤ Formalism.MainNotions.szCond L := by linarith
  have h36 : Formalism.MainNotions.szCond L ≤ Formalism.MainNotions.szCond L ^ 36 := le_self_pow₀ hc1 (by norm_num)
  have h150 : Formalism.MainNotions.szCond L ^ 36 ≤ Formalism.MainNotions.szCond L ^ 36 * (D.R.t : ℝ) ^ 150 :=
    le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1)
  have hsb : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hfin : D.host.rdE ≤ L.sc.b := hc.trans (h36.trans (h150.trans (hCond.trans hsb)))
  have := Real.log_le_log (by linarith) hfin
  rwa [show Real.log L.sc.b = L.sc.L by unfold Scale.b; exact Real.log_exp _] at this

/- English proof (translation)
Establish `h` using `hEta.2.2.2.2.2.2.2.2`. Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hxe : 1 ≤ L.sc.x ^ L.sc.eps` using `Real.one_le_rpow hx1.le L.sc.eps_pos.le`. Establish `hb0 : 0 < L.sc.b` using `by unfold Scale.b; exact Real.exp_pos _`.

Establish `hb' : 0 ≤ L.sc.b'` using `by unfold Scale.b' Scale.a Scale.X' Scale.b; positivity`. Establish `hm1 : (1 : ℝ) ≤ D.R.m`. Establish `: 1 ≤ D.R.m` using `by have := D.R.two_le_m; omega`. Conclude with `this` after adjusting the coercions. Establish `hmk : (D.R.m : ℝ) ≤ D.R.k`.

Establish `: D.R.m ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions. Establish `hmr : (D.R.m : ℝ) ≤ D.R.r`. Establish `: D.R.m ≤ D.R.r` using `by unfold Ranks.r; have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions.

Establish `hd0` using `L.thickDensity_pos`. Establish `hd1` using `L.thickDensity_le_one`. Establish `hS0` using `L.Sc_pos`. Unfold `Formalism.MainNotions.szlA at h`. Establish `hmd : 0 < (D.R.m : ℝ) * L.de2` using `mul_pos (by linarith) hd0`.

Rewrite `h` using `[← mul_div_assoc, div_le_iff₀ hmd]`. Establish `l1 : (D.R.m : ℝ) * L.sc.b' ≤ (D.R.r : ℝ) * (L.sc.b' + L.Sc)` using `mul_le_mul hmr (by linarith) hb' (by linarith)`. Establish `l2 : (D.R.m : ℝ) * L.sc.b' * 2 ≤ (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x` using `mul_le_mul l1 hlx (by norm_num) (by positivity)`. Establish `l3 : (D.R.m : ℝ) * 1 ≤ (D.R.k : ℝ) * L.sc.x ^ L.sc.eps` using `mul_le_mul hmk hxe (by norm_num) (by linarith)`. Establish `l4 : (D.R.m : ℝ) * L.sc.b' * 2 * ((D.R.m : ℝ) * 1) ≤ (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * ((D.R.k : ℝ) * L.sc.x ^ L.sc.eps)` using `mul_le_mul l2 l3 (by positivity) (by positivity)`.

Establish `u1 : L.de2 * D.R.m * L.sc.b * ((D.R.m : ℝ) * L.de2) ≤ (D.R.m : ℝ) * D.R.m * L.sc.b`. Establish `e : L.de2 * D.R.m * L.sc.b * ((D.R.m : ℝ) * L.de2) = (L.de2 * L.de2) * ((D.R.m : ℝ) * D.R.m * L.sc.b)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Establish `: L.de2 * L.de2 ≤ 1` using `by nlinarith`.

Conclude with `mul_le_of_le_one_left (by positivity) this`. Establish `fin : (D.R.m : ℝ) * D.R.m * (2 * L.sc.b') ≤ (D.R.m : ℝ) * D.R.m * L.sc.b`. Establish `e : (D.R.m : ℝ) * L.sc.b' * 2 * ((D.R.m : ℝ) * 1) = (D.R.m : ℝ) * D.R.m * (2 * L.sc.b')` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_of_mul_le_mul_left fin (by positivity)`.
-/
theorem bprime_le_half (D : D7) (L : SizeData₂ D) (hEta : Formalism.MainNotions.SizeEta L) (hlx : 2 ≤ Real.log L.sc.x) :
    2 * L.sc.b' ≤ L.sc.b := by
  have h := hEta.2.2.2.2.2.2.2.2
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hxe : 1 ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb0 : 0 < L.sc.b := by unfold Scale.b; exact Real.exp_pos _
  have hb' : 0 ≤ L.sc.b' := by unfold Scale.b' Scale.a Scale.X' Scale.b; positivity
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by
    have : D.R.m ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by
    have : D.R.m ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hd0 := L.thickDensity_pos
  have hd1 := L.thickDensity_le_one
  have hS0 := L.Sc_pos
  unfold Formalism.MainNotions.szlA at h
  have hmd : 0 < (D.R.m : ℝ) * L.de2 := mul_pos (by linarith) hd0
  rw [← mul_div_assoc, div_le_iff₀ hmd] at h

  have l1 : (D.R.m : ℝ) * L.sc.b' ≤ (D.R.r : ℝ) * (L.sc.b' + L.Sc) :=
    mul_le_mul hmr (by linarith) hb' (by linarith)
  have l2 : (D.R.m : ℝ) * L.sc.b' * 2 ≤ (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x :=
    mul_le_mul l1 hlx (by norm_num) (by positivity)
  have l3 : (D.R.m : ℝ) * 1 ≤ (D.R.k : ℝ) * L.sc.x ^ L.sc.eps := mul_le_mul hmk hxe (by norm_num) (by linarith)
  have l4 : (D.R.m : ℝ) * L.sc.b' * 2 * ((D.R.m : ℝ) * 1) ≤
      (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * ((D.R.k : ℝ) * L.sc.x ^ L.sc.eps) :=
    mul_le_mul l2 l3 (by positivity) (by positivity)

  have u1 : L.de2 * D.R.m * L.sc.b * ((D.R.m : ℝ) * L.de2) ≤ (D.R.m : ℝ) * D.R.m * L.sc.b := by
    have e : L.de2 * D.R.m * L.sc.b * ((D.R.m : ℝ) * L.de2) = (L.de2 * L.de2) * ((D.R.m : ℝ) * D.R.m * L.sc.b) := by
      ring
    rw [e]
    have : L.de2 * L.de2 ≤ 1 := by nlinarith
    exact mul_le_of_le_one_left (by positivity) this
  have fin : (D.R.m : ℝ) * D.R.m * (2 * L.sc.b') ≤ (D.R.m : ℝ) * D.R.m * L.sc.b := by
    have e : (D.R.m : ℝ) * L.sc.b' * 2 * ((D.R.m : ℝ) * 1) = (D.R.m : ℝ) * D.R.m * (2 * L.sc.b') := by ring
    linarith
  exact le_of_mul_le_mul_left fin (by positivity)

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -⟩` from `hS`. Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hk0 : (0 : ℝ) < D.R.k`. Establish `: 0 < D.R.k` using `by have := D.R.m_add_three_le_k; omega`.

Conclude with `this` after adjusting the coercions. Establish `h1` using `hBot t`. Establish `hLa0 : 0 ≤ L.LaG` using `le_trans (Real.rpow_pos_of_pos hx0 _).le hLa.1`. Establish `h2 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k` using `div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hx0 _).le (Real.log_nonneg hx1.le)) hLa0) hk0.le`. Establish `h3 : L.sc.x ^ (-2 : ℝ) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)`.

Establish `hb' : 0 ≤ L.sc.b'`. Unfold `Scale.b' Scale.a Scale.X' Scale.b`. Check the signs of the components of the expression. Establish `hR : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k + L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k ≤ L.sc.x ^ (-2 : ℝ)` using `hRho`. Establish `h4 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1`.

Establish `: 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k)` using `by ring`. Establish `h0 : 0 ≤ Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k`. Unfold `Formalism.MainNotions.szNst Scale.delta1`. Use `Real.rpow_pos_of_pos hx0 (-(L.sc.eps / 8))` as an intermediate fact. Use `Real.rpow_pos_of_pos hx0 L.sc.eps` as an intermediate fact.

Check the signs of the components of the expression. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k = Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k * L.sc.b'` using `by ring`. Rewrite `h1` using `[h5]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem bT_le_two (D : D7) (L : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt L) (t : D.host.TT) : (L.bT t : ℝ) ≤ 2 * L.sc.b' := by
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -⟩ := hS
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hk0 : (0 : ℝ) < D.R.k := by
    have : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have h1 := hBot t
  have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_pos_of_pos hx0 _).le hLa.1
  have h2 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k :=
    div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hx0 _).le (Real.log_nonneg hx1.le)) hLa0) hk0.le
  have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)
  have hb' : 0 ≤ L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    positivity
  have hR : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k +
      L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k ≤ L.sc.x ^ (-2 : ℝ) := hRho
  have h4 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 := by
    have : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
        4 * (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
    have h0 : 0 ≤ Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k := by
      unfold Formalism.MainNotions.szNst Scale.delta1
      have := Real.rpow_pos_of_pos hx0 (-(L.sc.eps / 8))
      have := Real.rpow_pos_of_pos hx0 L.sc.eps
      positivity
    linarith
  have h5 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k * L.sc.b' := by ring
  rw [h5] at h1
  nlinarith

/- English proof (translation)
Establish `hbT` using `bT_le_two D L hS`. Establish `hEta : Formalism.MainNotions.SizeEta L` using `hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1`. Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hbb` using `bprime_le_half D L hEta hlx`.

Establish `hL1 : 1 ≤ L.sc.L` using `by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le`. Establish `hb2 : 2 ≤ L.sc.b`. Unfold `Scale.b`. Use `Real.add_one_le_exp L.sc.L` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hb' : 0 ≤ L.sc.b'` using `by unfold Scale.b' Scale.a Scale.X' Scale.b; positivity`. Establish `hn1 : (1 : ℝ) ≤ D.R.n`. Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`. Conclude with `this` after adjusting the coercions. Establish `hw' : L.sc.w'' D.R.n ≤ L.sc.b'`.

Unfold `Scale.w''`. Conclude with `div_le_self hb' (by nlinarith)`. Establish `hbx : L.sc.b' / L.sc.x ≤ L.sc.b'` using `div_le_self hb' hx1.le`. Establish `hbx0 : 0 ≤ L.sc.b' / L.sc.x` using `by positivity`. Establish `hη0` using `L.etaSz_pos`.

Establish `ht4 : (4 : ℝ) ≤ D.R.t`. Establish `: 4 ≤ D.R.t` using `by have := D.R.rank_add_five_le; omega`. Conclude with `this` after adjusting the coercions. Establish `hk1 : (1 : ℝ) ≤ D.R.k`. Establish `: 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`.

Conclude with `this` after adjusting the coercions. Establish `hf1 : (1 : ℝ) ≤ D.R.f`. Establish `: 1 ≤ D.R.f` using `by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega`. Conclude with `this` after adjusting the coercions. Establish `hη : 4 * L.etaSz ≤ L.sc.b`.

Establish `e1` using `hEta.2.1`. Rewrite `e1` using `[le_div_iff₀ (by positivity)]`. Establish `e2 : (4 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3`. Establish `a1 : (4 : ℝ) ≤ (D.R.t : ℝ) ^ 3` using `by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ D.R.t) (by linarith : (0:ℝ) ≤ D.R.t)]`. Establish `a2 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3` using `one_le_pow₀ hk1`.

Establish `a3 : (4 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Establish `hwj : DV.wSz D j τ = wj D j τ`. Unfold `DV.wSz wj`.

Rewrite using `[dif_pos ⟨h1, h2⟩, dif_pos (by omega)]`. Rewrite using `[hwj]`. Distinguish the cases in `htop : ((D.eTau τ : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces`. Unfold `Host.topPlaces at htop`. Take `⟨a, ha, hae⟩` from `Finset.mem_image.1 htop`.

Establish `hw` using `L.win_top j h1 h2 τ ⟨a, ha⟩ hae.symm`. Establish `g1` using `L.bT_ge ⟨a, ha⟩`. Establish `g2` using `hbT ⟨a, ha⟩`. Apply the tactic sequence `constructor <;> linarith`. Distinguish the cases in `hthick : ((D.eTau τ : D.R.Psi) : D.R.GG) ∈ D.host.thickPlaces`.

Establish `hw` using `L.win_thick j h1 h2 τ hthick`. Apply the tactic sequence `constructor <;> linarith`. Establish `hw` using `L.win_thin j h1 h2 τ ⟨(D.eTau τ).2, htop, hthick⟩`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem size_window (D : D7) (L : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt L) (hlx : 2 ≤ Real.log L.sc.x)
    (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) :
    L.sc.w'' D.R.n ≤ DV.wSz D j τ ∧ DV.wSz D j τ ≤ 2 * L.sc.b := by
  have hbT := bT_le_two D L hS
  have hEta : Formalism.MainNotions.SizeEta L := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hbb := bprime_le_half D L hEta hlx
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb2 : 2 ≤ L.sc.b := by
    unfold Scale.b; have := Real.add_one_le_exp L.sc.L; linarith
  have hb' : 0 ≤ L.sc.b' := by unfold Scale.b' Scale.a Scale.X' Scale.b; positivity
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hw' : L.sc.w'' D.R.n ≤ L.sc.b' := by
    unfold Scale.w''
    exact div_le_self hb' (by nlinarith)
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb' hx1.le
  have hbx0 : 0 ≤ L.sc.b' / L.sc.x := by positivity
  have hη0 := L.etaSz_pos
  have ht4 : (4 : ℝ) ≤ D.R.t := by
    have : 4 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
    exact_mod_cast this
  have hη : 4 * L.etaSz ≤ L.sc.b := by
    have e1 := hEta.2.1
    rw [le_div_iff₀ (by positivity)] at e1
    have e2 : (4 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 := by
      have a1 : (4 : ℝ) ≤ (D.R.t : ℝ) ^ 3 := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ D.R.t) (by linarith : (0:ℝ) ≤ D.R.t)]
      have a2 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ hk1
      have a3 : (4 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f := by nlinarith
      nlinarith
    nlinarith
  have hwj : DV.wSz D j τ = wj D j τ := by
    unfold DV.wSz wj
    rw [dif_pos ⟨h1, h2⟩, dif_pos (by omega)]
  rw [hwj]
  by_cases htop : ((D.eTau τ : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces
  · unfold Host.topPlaces at htop
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.1 htop
    have hw := L.win_top j h1 h2 τ ⟨a, ha⟩ hae.symm
    have g1 := L.bT_ge ⟨a, ha⟩
    have g2 := hbT ⟨a, ha⟩
    constructor <;> linarith
  · by_cases hthick : ((D.eTau τ : D.R.Psi) : D.R.GG) ∈ D.host.thickPlaces
    · have hw := L.win_thick j h1 h2 τ hthick
      constructor <;> linarith
    · have hw := L.win_thin j h1 h2 τ ⟨(D.eTau τ).2, htop, hthick⟩
      constructor <;> linarith

/- English proof (translation)
Take `⟨-, -, -, -, -, hCond, hQD, -, -, -, -, -, -, hEta, -, -, hDel, hW, -⟩` from `hS`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Use `set y : ℝ := L.sc.x ^ (L.sc.eps / 4) with hyd`. Establish `hLy : L.sc.L = y ^ 4`.

Unfold `Scale.L`. Rewrite using `[hyd, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hy3 : (27 : ℝ) ≤ y ^ 3`. Use `pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hy 3` as an intermediate fact. Evaluate the numerical expressions using `at this`. Conclude with `this`. Establish `hL27 : 27 * y ≤ L.sc.L`.

Rewrite using `[hLy, show y ^ 4 = y ^ 3 * y by ring]`. Conclude with `mul_le_mul_of_nonneg_right hy3 (by linarith)`. Establish `hL81 : 81 ≤ L.sc.L` using `by linarith`. Establish `hw0 : 0 ≤ L.sc.w'' D.R.n`. Unfold `Scale.w'' Scale.b' Scale.a Scale.X' Scale.b`.

Check the signs of the components of the expression. Establish `hb0 : 0 < L.sc.b` using `by unfold Scale.b; exact Real.exp_pos _`. Establish `hlb : Real.log L.sc.b = L.sc.L` using `by unfold Scale.b; exact Real.log_exp _`. Establish `hη0` using `L.etaSz_pos`. Establish `hS0` using `L.Sc_pos`.

Establish `hk0 : (0 : ℝ) < D.R.k`. Establish `: 0 < D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions. Establish `hkt : (D.R.k : ℝ) ≤ D.R.t`. Establish `: D.R.k ≤ D.R.t` using `by have := D.R.rank_add_five_le; have := D.R.two_le_m; omega`.

Conclude with `this` after adjusting the coercions. Establish `ht0 : (0 : ℝ) < D.R.t` using `by linarith`. Establish `hA : p * L.etaSz ≤ L.sc.w'' D.R.n / 2`. Establish `h1 : p * L.etaSz ≤ 2 * D.R.t * L.etaSz` using `mul_le_mul_of_nonneg_right hp2t hη0.le`. Establish `h2` using `hEta.2.2.2.1`.

Establish `h3 : L.sc.w'' D.R.n / L.sc.x * L.sc.x = L.sc.w'' D.R.n` using `by field_simp`. Establish `h4 : 0 ≤ L.sc.w'' D.R.n / L.sc.x` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hDel0 : (0 : ℝ) < (D.s.Del : ℝ)`. Use `L.Sc_eq` as an intermediate fact.

Assume the negation of the conclusion as `hneg`. Use `push Not at hneg`. Establish `: L.Sc ≤ 0` using `by rw [L.Sc_eq]; nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq2` using `two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.1)`.

Establish `hd2` using `two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.2.2.2.1)`. Establish `hc1 : 1 ≤ Formalism.MainNotions.szCond L`. Unfold `Formalism.MainNotions.szCond`. Establish `hq' : (2 : ℝ) ≤ D.host.q` using `by exact_mod_cast hq2`. Establish `hd' : (2 : ℝ) ≤ D.host.d` using `by exact_mod_cast hd2`.

Establish `hn1 : (1 : ℝ) ≤ D.R.n`. Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`. Conclude with `this` after adjusting the coercions. Establish `: (1 : ℝ) ≤ 4 * D.R.n` using `by linarith`. Establish `hQ : (1 : ℝ) ≤ D.host.QS` using `by exact_mod_cast D.host.QS_pos`.

Establish `: (1 : ℝ) ≤ D.host.QS * D.host.q` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hlt : Real.log D.R.t ≤ L.sc.L / 300`. Establish `h1 : (D.R.t : ℝ) ^ 150 ≤ Real.sqrt L.sc.b` using `le_trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc1)) hCond`. Establish `h2` using `Real.log_le_log (by positivity) h1`.

Rewrite `h2` using `[Real.log_pow, Real.log_sqrt hb0.le, hlb]`. Move the coercions through the operations in `at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlk : Real.log D.R.k ≤ L.sc.L / 300` using `(Real.log_le_log hk0 hkt).trans hlt`. Establish `hlD : Real.log (D.s.Del : ℝ) ≤ y / 2` using `hDel.2.2.1`.

Establish `h16 : Real.log 16 = 4 * Real.log 2`. Rewrite using `[show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num`. Establish `hB : 16 * (D.R.t : ℝ) * D.R.k * (D.s.Del : ℝ) ≤ L.sc.w'' D.R.n`. Use `le_trans ?_ hW` and prove the remaining obligations. Establish `hpos : 0 < 16 * (D.R.t : ℝ) * D.R.k * (D.s.Del : ℝ)` using `by positivity`.

Rewrite using `[← Real.log_le_log_iff hpos (Real.sqrt_pos.2 hb0), Real.log_sqrt hb0.le, hlb, Real.log_mul (by positivity) hDel0.ne', Real.log_mul (by positivity) hk0.ne', Real.log_mul (by norm_num) ht0.ne', h16]`. Use `Real.log_two_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hBS : p * L.Sc ≤ L.sc.w'' D.R.n / 2`. Establish `h1 : p * L.Sc ≤ 2 * D.R.t * L.Sc` using `mul_le_mul_of_nonneg_right hp2t hS0.le`.

Establish `h2 : 2 * (D.R.t : ℝ) * L.Sc = (16 * (D.R.t : ℝ) * D.R.k * (D.s.Del : ℝ)) / 2`. Rewrite using `[L.Sc_eq]`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: p * (L.Sc + L.etaSz) = p * L.Sc + p * L.etaSz` using `by ring`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mul_widths_le (D : D7) (L : SizeData₂ D) (p : ℝ)
    (hp2t : p ≤ 2 * D.R.t) (hS : Formalism.MainNotions.SizesAt L)
    (hx4 : 4 ≤ L.sc.x) (hy : 3 ≤ L.sc.x ^ (L.sc.eps / 4)) :
    p * (L.Sc + L.etaSz) ≤ L.sc.w'' D.R.n := by
  obtain ⟨-, -, -, -, -, hCond, hQD, -, -, -, -, -, -, hEta, -, -, hDel, hW, -⟩ := hS
  have hx0 : 0 < L.sc.x := by linarith
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  set y : ℝ := L.sc.x ^ (L.sc.eps / 4) with hyd
  have hLy : L.sc.L = y ^ 4 := by
    unfold Scale.L
    rw [hyd, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1; push_cast; ring
  have hy3 : (27 : ℝ) ≤ y ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hy 3
    norm_num at this; exact this
  have hL27 : 27 * y ≤ L.sc.L := by
    rw [hLy, show y ^ 4 = y ^ 3 * y by ring]
    exact mul_le_mul_of_nonneg_right hy3 (by linarith)
  have hL81 : 81 ≤ L.sc.L := by linarith
  have hw0 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w'' Scale.b' Scale.a Scale.X' Scale.b; positivity
  have hb0 : 0 < L.sc.b := by unfold Scale.b; exact Real.exp_pos _
  have hlb : Real.log L.sc.b = L.sc.L := by unfold Scale.b; exact Real.log_exp _
  have hη0 := L.etaSz_pos
  have hS0 := L.Sc_pos
  have hk0 : (0 : ℝ) < D.R.k := by
    have : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hkt : (D.R.k : ℝ) ≤ D.R.t := by
    have : D.R.k ≤ D.R.t := by have := D.R.rank_add_five_le; have := D.R.two_le_m; omega
    exact_mod_cast this
  have ht0 : (0 : ℝ) < D.R.t := by linarith

  have hA : p * L.etaSz ≤ L.sc.w'' D.R.n / 2 := by
    have h1 : p * L.etaSz ≤ 2 * D.R.t * L.etaSz := mul_le_mul_of_nonneg_right hp2t hη0.le
    have h2 := hEta.2.2.2.1
    have h3 : L.sc.w'' D.R.n / L.sc.x * L.sc.x = L.sc.w'' D.R.n := by field_simp
    have h4 : 0 ≤ L.sc.w'' D.R.n / L.sc.x := by positivity
    nlinarith

  have hDel0 : (0 : ℝ) < (D.s.Del : ℝ) := by
    have := L.Sc_eq
    by_contra hneg
    push Not at hneg
    have : L.Sc ≤ 0 := by rw [L.Sc_eq]; nlinarith
    linarith
  have hq2 := two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.1)
  have hd2 := two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.2.2.2.1)
  have hc1 : 1 ≤ Formalism.MainNotions.szCond L := by
    unfold Formalism.MainNotions.szCond
    have hq' : (2 : ℝ) ≤ D.host.q := by exact_mod_cast hq2
    have hd' : (2 : ℝ) ≤ D.host.d := by exact_mod_cast hd2
    have hn1 : (1 : ℝ) ≤ D.R.n := by
      have : 1 ≤ D.R.n := D.R.ord_pos
      exact_mod_cast this
    have : (1 : ℝ) ≤ 4 * D.R.n := by linarith
    have hQ : (1 : ℝ) ≤ D.host.QS := by exact_mod_cast D.host.QS_pos
    have : (1 : ℝ) ≤ D.host.QS * D.host.q := by nlinarith
    nlinarith
  have hlt : Real.log D.R.t ≤ L.sc.L / 300 := by
    have h1 : (D.R.t : ℝ) ^ 150 ≤ Real.sqrt L.sc.b :=
      le_trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc1)) hCond
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow, Real.log_sqrt hb0.le, hlb] at h2
    push_cast at h2
    linarith
  have hlk : Real.log D.R.k ≤ L.sc.L / 300 := (Real.log_le_log hk0 hkt).trans hlt
  have hlD : Real.log (D.s.Del : ℝ) ≤ y / 2 := hDel.2.2.1
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hB : 16 * (D.R.t : ℝ) * D.R.k * (D.s.Del : ℝ) ≤ L.sc.w'' D.R.n := by
    refine le_trans ?_ hW
    have hpos : 0 < 16 * (D.R.t : ℝ) * D.R.k * (D.s.Del : ℝ) := by positivity
    rw [← Real.log_le_log_iff hpos (Real.sqrt_pos.2 hb0), Real.log_sqrt hb0.le, hlb,
      Real.log_mul (by positivity) hDel0.ne', Real.log_mul (by positivity) hk0.ne',
      Real.log_mul (by norm_num) ht0.ne', h16]
    have := Real.log_two_lt_d9
    linarith
  have hBS : p * L.Sc ≤ L.sc.w'' D.R.n / 2 := by
    have h1 : p * L.Sc ≤ 2 * D.R.t * L.Sc := mul_le_mul_of_nonneg_right hp2t hS0.le
    have h2 : 2 * (D.R.t : ℝ) * L.Sc = (16 * (D.R.t : ℝ) * D.R.k * (D.s.Del : ℝ)) / 2 := by
      rw [L.Sc_eq]; ring
    linarith
  have : p * (L.Sc + L.etaSz) = p * L.Sc + p * L.etaSz := by ring
  linarith

/- English proof (translation)
Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hm1 : (1 : ℝ) ≤ D.R.m`. Establish `: 1 ≤ D.R.m` using `by have := D.R.two_le_m; omega`. Conclude with `this` after adjusting the coercions. Establish `hmk : (D.R.m : ℝ) ≤ D.R.k`.

Establish `: D.R.m ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions. Establish `hf0 : 0 < D.R.f` using `by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega`. Establish `hf1 : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast hf0`. Establish `hr2 : 2 ≤ D.R.r` using `by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`.

Establish `hD1 : (1 : ℝ) ≤ (T.Dp : ℝ)`. Establish `: 1 ≤ T.Dp`. Rewrite using `[T.Dp_eq]`. Conclude with `Nat.mul_pos hf0 (Nat.choose_pos hr2)`. Conclude with `this` after adjusting the coercions.

Establish `hxCp : 1 ≤ L.sc.x ^ T.Cp` using `Real.one_le_rpow hx1.le T.Cp_nonneg`. Establish `hmd : 0 < (D.R.m : ℝ) * L.de2` using `mul_pos (by linarith) L.thickDensity_pos`. Establish `hPT : T.PP ≤ (T.TO : ℝ)`. Use `le_trans ?_ T.TO_ge` and prove the remaining obligations. Rewrite using `[le_div_iff₀ hmd]`.

Establish `b0 : (D.R.m : ℝ) * L.de2 ≤ D.R.k`. Use `L.thickDensity_le_one` as an intermediate fact. Use `L.thickDensity_pos` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `b1 : T.PP * ((D.R.m : ℝ) * L.de2) ≤ T.PP * D.R.k` using `mul_le_mul_of_nonneg_left b0 (by linarith)`.

Establish `b2 : T.PP ≤ T.PP ^ 4` using `le_self_pow₀ h1 (by norm_num)`. Establish `b3 : T.PP ^ 4 ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3` using `le_mul_of_one_le_right (by positivity) (one_le_pow₀ hD1)`. Establish `b4 : T.PP * D.R.k ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k` using `mul_le_mul_of_nonneg_right (b2.trans b3) (by linarith)`. Establish `b5 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f` using `le_mul_of_one_le_right (by positivity) hf1`. Establish `b6 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ T.Cp` using `le_mul_of_one_le_right (by positivity) hxCp`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hTt : (T.TO : ℝ) ≤ D.R.t`. Establish `: T.TO ≤ D.R.t`. Establish `s` using `T.split`. Establish `n1` using `T.nP_ge`.

Establish `n2 : T.TO ≤ T.TO * T.nWn` using `Nat.le_mul_of_pos_right _ hnW`. Establish `n3 : D.R.r ≤ 8 * D.R.f * D.R.r` using `Nat.le_mul_of_pos_left _ (by omega)`. Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions. Conclude with `⟨hPT, by linarith⟩`.
-/
theorem parameterPrecision_le_length_and_rank (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : ParamsT D L P)
    (h1 : 1 ≤ T.PP) (hnW : 1 ≤ T.nWn) :
    T.PP ≤ (T.TO : ℝ) ∧ T.PP ≤ D.R.t := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by
    have : D.R.m ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hf0 : 0 < D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf0
  have hr2 : 2 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hD1 : (1 : ℝ) ≤ (T.Dp : ℝ) := by
    have : 1 ≤ T.Dp := by
      rw [T.Dp_eq]
      exact Nat.mul_pos hf0 (Nat.choose_pos hr2)
    exact_mod_cast this
  have hxCp : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow hx1.le T.Cp_nonneg
  have hmd : 0 < (D.R.m : ℝ) * L.de2 := mul_pos (by linarith) L.thickDensity_pos
  have hPT : T.PP ≤ (T.TO : ℝ) := by
    refine le_trans ?_ T.TO_ge
    rw [le_div_iff₀ hmd]
    have b0 : (D.R.m : ℝ) * L.de2 ≤ D.R.k := by
      have := L.thickDensity_le_one; have := L.thickDensity_pos; nlinarith
    have b1 : T.PP * ((D.R.m : ℝ) * L.de2) ≤ T.PP * D.R.k := mul_le_mul_of_nonneg_left b0 (by linarith)
    have b2 : T.PP ≤ T.PP ^ 4 := le_self_pow₀ h1 (by norm_num)
    have b3 : T.PP ^ 4 ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hD1)
    have b4 : T.PP * D.R.k ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k :=
      mul_le_mul_of_nonneg_right (b2.trans b3) (by linarith)
    have b5 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f :=
      le_mul_of_one_le_right (by positivity) hf1
    have b6 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f ≤
        T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ T.Cp :=
      le_mul_of_one_le_right (by positivity) hxCp
    linarith
  have hTt : (T.TO : ℝ) ≤ D.R.t := by
    have : T.TO ≤ D.R.t := by
      have s := T.split
      have n1 := T.nP_ge
      have n2 : T.TO ≤ T.TO * T.nWn := Nat.le_mul_of_pos_right _ hnW
      have n3 : D.R.r ≤ 8 * D.R.f * D.R.r := Nat.le_mul_of_pos_left _ (by omega)
      omega
    exact_mod_cast this
  exact ⟨hPT, by linarith⟩

/- English proof (translation)
Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hL1 : 1 ≤ L.sc.L` using `by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le`. Establish `hf1 : (1 : ℝ) ≤ D.R.f`. Establish `: 1 ≤ D.R.f` using `by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega`. Conclude with `this` after adjusting the coercions.

Establish `hr1 : (1 : ℝ) ≤ D.R.r`. Establish `: 1 ≤ D.R.r` using `by unfold Ranks.r; have := D.R.two_le_m; omega`. Conclude with `this` after adjusting the coercions. Establish `hZ1 : (1 : ℝ) ≤ zBase L`. Unfold `zBase`.

Establish `: (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[T.PP_eq]`. Establish `h1` using `Real.one_le_rpow hZ1 (by linarith [T.eP_ge] : 0 ≤ T.eP)`. Establish `h2` using `T.one_le_CP`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_le_parPP (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : ParamsT D L P) : 1 ≤ T.PP := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ D.R.r := by
    have : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
    exact_mod_cast this
  have hZ1 : (1 : ℝ) ≤ zBase L := by
    unfold zBase
    have : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    nlinarith
  rw [T.PP_eq]
  have h1 := Real.one_le_rpow hZ1 (by linarith [T.eP_ge] : 0 ≤ T.eP)
  have h2 := T.one_le_CP
  nlinarith

/- English proof (translation)
Use `le_trans ?_ T.nW_lo.1` and prove the remaining obligations. Establish `hf : 0 < D.R.f` using `by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega`. Establish `hr : 0 < D.R.r` using `by unfold Ranks.r; have := D.R.two_le_m; omega`. Conclude with `Nat.mul_pos (Nat.mul_pos hf hr) (Nat.succ_pos _)`.
-/
theorem one_le_nWn (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : ParamsT D L P) : 1 ≤ T.nWn := by
  refine le_trans ?_ T.nW_lo.1
  have hf : 0 < D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  have hr : 0 < D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  exact Nat.mul_pos (Nat.mul_pos hf hr) (Nat.succ_pos _)

def sgR (D : D7) (τ : D.what₂.Tau) (i : ℕ) : ℝ := ((DV.sigPar D τ i : ℚ) : ℝ)

/- English proof (translation)
Unfold `DV.sigPar`. Rewrite using `[dif_neg (by omega)]`. Simplify using `only [Nat.add_sub_cancel_left]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sigPar_low (D : D7) (τ : D.what₂.Tau) (a : ℕ) :
    DV.sigPar D τ (D.R.k - 1 + a) = -(if h : a < D.R.m then (D.hc τ).b ⟨a, h⟩ else 0) := by
  unfold DV.sigPar
  rw [dif_neg (by omega)]
  simp only [Nat.add_sub_cancel_left]
  split_ifs <;> simp

/- English proof (translation)
Unfold `sgR DV.sigPar`. Rewrite using `[dif_pos h]`.
-/
theorem sgR_cloud (D : D7) (τ : D.what₂.Tau) (i : ℕ) (h : i < D.R.k - 1) :
    sgR D τ i = (((D.hc τ).v ⟨i, h⟩ : ℚ) : ℝ) := by
  unfold sgR DV.sigPar
  rw [dif_pos h]

/- English proof (translation)
Unfold `sgR`. Rewrite using `[sigPar_low, dif_pos h]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem sgR_low (D : D7) (τ : D.what₂.Tau) (a : ℕ) (h : a < D.R.m) :
    sgR D τ (D.R.k - 1 + a) = -(((D.hc τ).b ⟨a, h⟩ : ℚ) : ℝ) := by
  unfold sgR
  rw [sigPar_low, dif_pos h]
  push_cast
  rfl

/- English proof (translation)
Introduce `l hl`. Proceed by induction on `l, hl using Nat.le_induction with`. Consider the case `base => intro _`. Simplify using the standard rewrite rules. Consider the case `succ l hl ih`.

Introduce `h`. Establish `h1` using `ih (by omega)`. Establish `h2` using `hs l (by omega) h`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem steps_sum (s : ℕ → ℝ) (lo r : ℕ) (G : ℝ) (hs : ∀ i, lo ≤ i → i + 1 < r → G ≤ s i - s (i + 1)) (i : ℕ) (hi : lo ≤ i) :
    ∀ l, i ≤ l → l < r → ((l : ℝ) - i) * G ≤ s i - s l := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base => intro _; simp
  | succ l hl ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := hs l (by omega) h
    push_cast
    linarith

/- English proof (translation)
Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hm` using `D.R.two_le_m`. Break down `Nat.lt_trichotomy (i + 1) (D.R.k - 1) with h | h | h` into its components or cases. Rewrite using `[sgR_cloud D τ i (by omega), sgR_cloud D τ (i + 1) h]`.

Establish `e` using `D.s.cloud_gap D.u₀ τ i h`. Rewrite `e` using `[D.hcW_base]`. Establish `e'` using `congrArg (fun q : ℚ => (q : ℝ)) e`. Simplify using `only [Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat] at e'`. Rewrite using `[e']`.

Conclude with `h1`. Establish `e0 : i + 1 = D.R.k - 1 + 0` using `by omega`. Rewrite using `[sgR_cloud D τ i (by omega), e0, sgR_low D τ 0 (by omega)]`. Use `(L.cloud_v τ ⟨i, by omega⟩).1` as an intermediate fact. Use `h3 (by omega)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨a, ha⟩ : ∃ a, i = D.R.k - 1 + a` from `⟨i - (D.R.k - 1), by omega⟩`. Substitute `ha` using the available equality. Rewrite using `[sgR_low D τ a (by omega), Nat.add_assoc, sgR_low D τ (a + 1) (by omega)]`. Use `(P.nodes_gap τ a (by omega)).1` as an intermediate fact.

Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sgR_step (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (τ : D.what₂.Tau) (G : ℝ)
    (h1 : G ≤ 4 * ((D.s.Del : ℚ) : ℝ)) (h2 : G ≤ LevelStarExponents.h0 L)
    (h3 : ∀ hm : 0 < D.R.m, G ≤ (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ)) (i : ℕ) (hi : i + 1 < D.R.r) :
    G ≤ sgR D τ i - sgR D τ (i + 1) := by
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  rcases Nat.lt_trichotomy (i + 1) (D.R.k - 1) with h | h | h
  · rw [sgR_cloud D τ i (by omega), sgR_cloud D τ (i + 1) h]
    have e := D.s.cloud_gap D.u₀ τ i h
    rw [D.hcW_base] at e
    have e' := congrArg (fun q : ℚ => (q : ℝ)) e
    simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat] at e'
    rw [e']
    exact h1
  · have e0 : i + 1 = D.R.k - 1 + 0 := by omega
    rw [sgR_cloud D τ i (by omega), e0, sgR_low D τ 0 (by omega)]
    have := (L.cloud_v τ ⟨i, by omega⟩).1
    have := h3 (by omega)
    linarith
  · obtain ⟨a, ha⟩ : ∃ a, i = D.R.k - 1 + a := ⟨i - (D.R.k - 1), by omega⟩
    subst ha
    rw [sgR_low D τ a (by omega), Nat.add_assoc, sgR_low D τ (a + 1) (by omega)]
    have := (P.nodes_gap τ a (by omega)).1
    push_cast at this
    linarith

/- English proof (translation)
Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hk` using `D.R.m_add_three_le_k`. Take `⟨a, ha⟩ : ∃ a, i = D.R.k - 1 + a` from `⟨i - (D.R.k - 1), by omega⟩`. Substitute `ha` using the available equality. Rewrite using `[sgR_low D τ a (by omega), Nat.add_assoc, sgR_low D τ (a + 1) (by omega)]`.

Use `(P.nodes_gap τ a (by omega)).1` as an intermediate fact. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sgR_step_low (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (τ : D.what₂.Tau) (i : ℕ) (hlo : D.R.k - 1 ≤ i)
    (hi : i + 1 < D.R.r) : LevelStarExponents.h0 L ≤ sgR D τ i - sgR D τ (i + 1) := by
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk := D.R.m_add_three_le_k
  obtain ⟨a, ha⟩ : ∃ a, i = D.R.k - 1 + a := ⟨i - (D.R.k - 1), by omega⟩
  subst ha
  rw [sgR_low D τ a (by omega), Nat.add_assoc, sgR_low D τ (a + 1) (by omega)]
  have := (P.nodes_gap τ a (by omega)).1
  push_cast at this
  linarith

/- English proof (translation)
Establish `h : 1 ≤ R.k + R.m` using `by have := R.two_le_m; omega`. Unfold `Ranks.r`. Move the coercions through the operations in `[Nat.cast_sub h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem r_cast (R : Ranks) : (R.r : ℝ) = (R.k : ℝ) + R.m - 1 := by
  have h : 1 ≤ R.k + R.m := by have := R.two_le_m; omega
  unfold Ranks.r
  push_cast [Nat.cast_sub h]
  ring

/- English proof (translation)
Unfold `DV.wSz`. Rewrite using `[dif_pos ⟨h1, h2⟩]`.
-/
theorem wSz_eq (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) :
    DV.wSz D j τ = (((D.hc τ).e ⟨j - 1, by omega⟩ : ℚ) : ℝ) := by
  unfold DV.wSz
  rw [dif_pos ⟨h1, h2⟩]

/- English proof (translation)
Establish `h` using `P.h0_ge.2.2.2.2.1`. Establish `h1 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3` using `by positivity`. Establish `h2 : (0 : ℝ) ≤ (D.R.t : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem six_le_h0 (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) : 6 ≤ LevelStarExponents.h0 L := by
  have h := P.h0_ge.2.2.2.2.1
  have h1 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
  have h2 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  linarith

/- English proof (translation)
Establish `hb` using `abs_le.1 (L.be_close τ ⟨0, hm⟩ ⟨j - 1, by omega⟩)`. Rewrite `hw` using `[wSz_eq D j h1 h2 τ]`. Move the coercions through the operations in `at hb`. Establish `he` using `L.etaSz_pos`. Establish `hm2 : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast D.R.two_le_m`.

Establish `ht : (0 : ℝ) ≤ (D.R.t : ℝ)` using `Nat.cast_nonneg _`. Establish `h3 : 2 * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz`. Use `mul_le_mul_of_nonneg_right ?_ he.le` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities. Establish `h4` using `P.mteta`.

Establish `h5 : LevelStarExponents.h0 L ≤ L.etaSz`. Unfold `LevelStarExponents.h0`. Conclude with `div_le_self he.le (by linarith)`. Combine the linear relations using `[hb.1]`.
-/
theorem minimalGap_le_first_lowerRowParameter (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau)
    (hw : L.sc.w'' D.R.n ≤ DV.wSz D j τ) (hm : 0 < D.R.m) : LevelStarExponents.h0 L ≤ (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) := by
  have hb := abs_le.1 (L.be_close τ ⟨0, hm⟩ ⟨j - 1, by omega⟩)
  rw [wSz_eq D j h1 h2 τ] at hw
  push_cast at hb
  have he := L.etaSz_pos
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have h3 : 2 * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
    refine mul_le_mul_of_nonneg_right ?_ he.le
    nlinarith
  have h4 := P.mteta
  have h5 : LevelStarExponents.h0 L ≤ L.etaSz := by
    unfold LevelStarExponents.h0
    exact div_le_self he.le (by linarith)
  linarith [hb.1]

/- English proof (translation)
Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hk` using `D.R.m_add_three_le_k`. Take `⟨a, ha⟩ : ∃ a, i = D.R.k - 1 + a` from `⟨i - (D.R.k - 1), by omega⟩`. Substitute `ha` using the available equality. Rewrite using `[sgR_low D τ a (by omega), wSz_eq D j h1 h2 τ]`.

Establish `hb` using `L.be_close τ ⟨a, by omega⟩ ⟨j - 1, by omega⟩`. Move the coercions through the operations in `at hb`. Rewrite using `[← abs_neg]`. Use `hb using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sgR_be (D : D7) (L : SizeData₂ D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) (i : ℕ)
    (hlo : D.R.k - 1 ≤ i) (hi : i < D.R.r) : |sgR D τ i + DV.wSz D j τ| ≤ L.etaSz := by
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk := D.R.m_add_three_le_k
  obtain ⟨a, ha⟩ : ∃ a, i = D.R.k - 1 + a := ⟨i - (D.R.k - 1), by omega⟩
  subst ha
  rw [sgR_low D τ a (by omega), wSz_eq D j h1 h2 τ]
  have hb := L.be_close τ ⟨a, by omega⟩ ⟨j - 1, by omega⟩
  push_cast at hb
  rw [← abs_neg]
  convert hb using 2
  ring

/- English proof (translation)
Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hL1 : 1 ≤ L.sc.L` using `by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le`. Establish `hk1 : (1 : ℝ) ≤ D.R.k`. Establish `: 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions.

Establish `hm1 : (1 : ℝ) ≤ D.R.m`. Establish `: 1 ≤ D.R.m` using `by have := D.R.two_le_m; omega`. Conclude with `this` after adjusting the coercions. Establish `hf1 : (1 : ℝ) ≤ D.R.f`. Establish `: 1 ≤ D.R.f` using `by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega`.

Conclude with `this` after adjusting the coercions. Establish `hr2 : 2 ≤ D.R.r` using `by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Establish `hr1 : (1 : ℝ) ≤ D.R.r` using `by exact_mod_cast (by omega : 1 ≤ D.R.r)`. Establish `hD1 : (1 : ℝ) ≤ (T.Dp : ℝ)`. Establish `: 1 ≤ T.Dp`.

Rewrite using `[T.Dp_eq]`. Establish `h1 : 0 < D.R.r.choose 2` using `Nat.choose_pos hr2`. Establish `h2 : 0 < D.R.f` using `by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega`. Conclude with `Nat.mul_pos h2 h1`. Conclude with `this` after adjusting the coercions.

Establish `hZ1 : (1 : ℝ) ≤ zBase L`. Unfold `zBase`. Establish `: (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hP1 : 1 ≤ T.PP`.

Rewrite using `[T.PP_eq]`. Establish `h1` using `Real.one_le_rpow hZ1 (by linarith [T.eP_ge] : 0 ≤ T.eP)`. Establish `h2` using `T.one_le_CP`. Use the polynomial consequences of the given equalities and inequalities. Establish `hxCp : 1 ≤ L.sc.x ^ T.Cp` using `Real.one_le_rpow hx1.le T.Cp_nonneg`.

Use `le_trans ?_ T.TO_ge` and prove the remaining obligations. Establish `a1 : T.PP ^ 2 ≤ T.PP ^ 4` using `pow_le_pow_right₀ hP1 (by norm_num)`. Establish `a2 : (T.Dp : ℝ) ^ 2 ≤ (T.Dp : ℝ) ^ 3` using `pow_le_pow_right₀ hD1 (by norm_num)`. Establish `a3 : T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k` using `by gcongr`. Establish `a4 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f` using `le_mul_of_one_le_right (by positivity) hf1`.

Establish `a5 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ T.Cp` using `le_mul_of_one_le_right (by positivity) hxCp`. Establish `hd : (D.R.m : ℝ) * L.de2 ≤ D.R.m`. Use `L.thickDensity_le_one` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Conclude with `div_le_div₀ (by positivity) (a3.trans (a4.trans a5)) (mul_pos (by linarith) L.thickDensity_pos) hd`.
-/
theorem len_le (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : ParamsT D L P) :
    T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) ≤ (T.TO : ℝ) := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
    exact_mod_cast this
  have hr2 : 2 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hr1 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hD1 : (1 : ℝ) ≤ (T.Dp : ℝ) := by
    have : 1 ≤ T.Dp := by
      rw [T.Dp_eq]
      have h1 : 0 < D.R.r.choose 2 := Nat.choose_pos hr2
      have h2 : 0 < D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
      exact Nat.mul_pos h2 h1
    exact_mod_cast this
  have hZ1 : (1 : ℝ) ≤ zBase L := by
    unfold zBase
    have : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    nlinarith
  have hP1 : 1 ≤ T.PP := by
    rw [T.PP_eq]
    have h1 := Real.one_le_rpow hZ1 (by linarith [T.eP_ge] : 0 ≤ T.eP)
    have h2 := T.one_le_CP
    nlinarith
  have hxCp : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow hx1.le T.Cp_nonneg
  refine le_trans ?_ T.TO_ge
  have a1 : T.PP ^ 2 ≤ T.PP ^ 4 :=
    pow_le_pow_right₀ hP1 (by norm_num)
  have a2 : (T.Dp : ℝ) ^ 2 ≤ (T.Dp : ℝ) ^ 3 := pow_le_pow_right₀ hD1 (by norm_num)
  have a3 : T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k := by gcongr
  have a4 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f :=
    le_mul_of_one_le_right (by positivity) hf1
  have a5 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f ≤
      T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ T.Cp :=
    le_mul_of_one_le_right (by positivity) hxCp
  have hd : (D.R.m : ℝ) * L.de2 ≤ D.R.m := by
    have := L.thickDensity_le_one; nlinarith
  exact div_le_div₀ (by positivity) (a3.trans (a4.trans a5)) (mul_pos (by linarith) L.thickDensity_pos) hd

/- English proof (translation)
Establish `hrN : (D.R.r : ℝ) ≤ (D.R.N D.R.m : ℝ)`. Establish `: D.R.r ≤ D.R.N D.R.m`. Unfold `Ranks.r Ranks.N`. Establish `h1 : D.R.m ≤ D.R.m * (D.R.t + 1)` using `Nat.le_mul_of_pos_right _ (Nat.succ_pos _)`. Use linear arithmetic over natural numbers and integers.

Conclude with `this` after adjusting the coercions. Establish `hr0 : (0 : ℝ) ≤ (D.R.r : ℝ)` using `Nat.cast_nonneg _`. Establish `hd0 : (0 : ℝ) ≤ (T.Dp : ℝ)` using `Nat.cast_nonneg _`. Establish `ht0 : (0 : ℝ) ≤ (D.R.t : ℝ)` using `Nat.cast_nonneg _`. Prove the components needed by the constructor for the conclusion.

Establish `g1 : (tt + T.Dp + 2) * (tt + T.Dp + 2 + 2 * (D.R.r : ℝ)) ≤ ((T.TO : ℝ) + T.Dp + 2) * ((T.TO : ℝ) + T.Dp + 2 + 2 * (D.R.N D.R.m : ℝ))` using `mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)`. Establish `g2` using `T.Del_gap`. Establish `g3 : (1 : ℝ) ≤ (tt + T.Dp + 2) * (tt + T.Dp + 2 + 2 * (D.R.r : ℝ))` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `q1 : 40 * ((T.Dp : ℝ) + 2) ≤ (T.TO : ℝ)` using `by exact_mod_cast T.TO_40`.

Establish `q2 : 2 * (D.R.r : ℝ) ≤ (T.TO : ℝ)`. Conclude with `le_trans (Nat.le_add_left _ _) T.TO_nW` after adjusting the coercions. Establish `g1 : (tt + T.Dp + 2) * (tt + T.Dp + 2 + 2 * (D.R.r : ℝ)) ≤ (41 / 40 * (T.TO : ℝ)) * (81 / 40 * (T.TO : ℝ))` using `mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)`. Establish `q3 : (80 : ℝ) ≤ (T.TO : ℝ)` using `by linarith`. Establish `q4` using `T.heightBound_ge_order_sq`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gap_le (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : ParamsT D L P) (tt : ℝ) (hT0 : 0 ≤ tt) (hTO : tt ≤ (T.TO : ℝ)) :
    (tt + T.Dp + 2) * (tt + T.Dp + 2 + 2 * (D.R.r : ℝ)) + 1 ≤ 4 * ((D.s.Del : ℚ) : ℝ) ∧
      (tt + T.Dp + 2) * (tt + T.Dp + 2 + 2 * (D.R.r : ℝ)) + 1 ≤ LevelStarExponents.h0 L := by
  have hrN : (D.R.r : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    have : D.R.r ≤ D.R.N D.R.m := by
      unfold Ranks.r Ranks.N
      have h1 : D.R.m ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      omega
    exact_mod_cast this
  have hr0 : (0 : ℝ) ≤ (D.R.r : ℝ) := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ (T.Dp : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  constructor
  · have g1 : (tt + T.Dp + 2) * (tt + T.Dp + 2 + 2 * (D.R.r : ℝ)) ≤
        ((T.TO : ℝ) + T.Dp + 2) * ((T.TO : ℝ) + T.Dp + 2 + 2 * (D.R.N D.R.m : ℝ)) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have g2 := T.Del_gap
    have g3 : (1 : ℝ) ≤ (tt + T.Dp + 2) * (tt + T.Dp + 2 + 2 * (D.R.r : ℝ)) := by nlinarith
    linarith
  · have q1 : 40 * ((T.Dp : ℝ) + 2) ≤ (T.TO : ℝ) := by exact_mod_cast T.TO_40
    have q2 : 2 * (D.R.r : ℝ) ≤ (T.TO : ℝ) := by
      exact_mod_cast le_trans (Nat.le_add_left _ _) T.TO_nW
    have g1 : (tt + T.Dp + 2) * (tt + T.Dp + 2 + 2 * (D.R.r : ℝ)) ≤
        (41 / 40 * (T.TO : ℝ)) * (81 / 40 * (T.TO : ℝ)) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have q3 : (80 : ℝ) ≤ (T.TO : ℝ) := by linarith
    have q4 := T.heightBound_ge_order_sq
    nlinarith

end GlobalTheory.CovTop.WtShape

end
