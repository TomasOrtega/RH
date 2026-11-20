import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bracket
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairFacts
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.WtBound
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KeptBlocksOfSLine

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

/- English proof (translation)
Establish `h` using `(coarse_bounds g P f hf hs hd).2`. Establish `hP' : (0 : ℝ) < P` using `by exact_mod_cast hP`. Rewrite using `[div_sub' (ne_of_gt hP'), div_lt_iff₀ hP']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem coarse_degree_gt_quotient {r : ℕ} (g P : ℕ) (f : Fin (r + 1) → ℕ) (hf : ∀ c, f c < P) (hs : ∑ c, f c ≤ g)
    (hd : P ∣ g - ∑ c, f c) (hP : 0 < P) :
    (g : ℝ) / P - ((r : ℝ) + 1) < (((g - ∑ c, f c) / P : ℕ) : ℝ) := by
  have h := (coarse_bounds g P f hf hs hd).2
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  rw [div_sub' (ne_of_gt hP'), div_lt_iff₀ hP']
  linarith

/- English proof (translation)
Establish `hk5` using `h.k5`. Establish `hk0 : 0 < X.k` using `by linarith`. Establish `hY` using `h.Y1`. Establish `hQ1` using `h.Q1`. Establish `hN2` using `h.N2`.

Establish `hN1` using `h.one_le_level_alt`. Establish `hLa` using `h.La1`. Establish `hb` using `h.bpos`. Establish `hba` using `h.ba`. Establish `hde` using `h.de6`.

Establish `hLaK` using `h.LaK`. Establish `hK240 : 240 * (X.N1 : ℝ) * X.La C0 < X.k`. Establish `h1 : 40 * (X.N1 : ℝ) * X.La C0 / X.k < 1 / 6` using `lt_of_le_of_lt hLaK hde`. Rewrite `h1` using `[div_lt_iff₀ hk0]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hNLa : 1 ≤ (X.N1 : ℝ) * X.La C0` using `one_le_mul_of_one_le_of_one_le hN1 hLa`. Establish `hk10 : 10 ≤ X.k` using `by nlinarith`. Establish `hLa4 : 4 * X.La C0 ≤ X.k` using `by nlinarith`. Establish `hkp : X.k ^ 2 ≤ (X.p : ℝ)`. Use `h.pk` as an intermediate fact.

Establish `hY2 : 1 ≤ X.Y ^ 2` using `one_le_pow₀ hY`. Use polynomial arithmetic with `[sq_nonneg X.k]`. Establish `hb4 : 4 * X.k ^ 3 * X.Q ≤ X.b'`. Establish `hHb` using `h.Hb`. Establish `hNQY : X.Q ≤ X.N * X.Q ^ 4 * X.Y`.

Establish `q4 : X.Q ≤ X.Q ^ 4` using `le_self_pow₀ hQ1 (by norm_num)`. Establish `hN1' : (1 : ℝ) ≤ X.N` using `by linarith`. Establish `: X.Q ^ 4 ≤ X.N * X.Q ^ 4 * X.Y`. Establish `hq : 0 ≤ X.Q ^ 4` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hN1' hq]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk3 : 0 ≤ 4 * X.k ^ 3` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `hQ0 : 0 < X.Q` using `by linarith`. Establish `hk3 : X.k ≤ X.k ^ 3` using `by nlinarith`.

Use `⟨?_, ?_, ?_, hkp, hk10, hLa, hLa4⟩` and prove the remaining obligations. Establish `hA0` using `h.half_ratio_le_segment_base_of_std j`. Establish `hfrac : X.N1 * X.La C0 / X.k ≤ 1 / 2`. Rewrite using `[div_le_iff₀ hk0]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hA0pos : 0 ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ)` using `le_trans (by positivity) hA0`. Establish `h1 : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) / 2 ≤ (A : ℝ)`. Establish `: ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 / 2) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k)` using `mul_le_mul_of_nonneg_left (by linarith) hA0pos`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : X.k ^ 3 ≤ (X.a : ℝ) / (2 * X.Q) / 2`.

Rewrite using `[div_div, le_div_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `i`. Establish `hPpos : 0 < (X.seg C0 CE1 CE2 j).P X.p i`.

Unfold `SegData.P; exact pow_pos (by have := h.p5; omega) _`. Establish `hPQ : ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) ≤ X.Q`. Establish `hl` using `h.levels j i`. Conclude with `le_trans hl.2.2.2.2 hl.2.2.2.1`. Establish `hgt` using `coarse_degree_gt_quotient ((X.seg C0 CE1 CE2 j).bTop i) ((X.seg C0 CE1 CE2 j).P X.p i) (rz i) (fun c => (hd.1 i c).1) (hd.2.1 i).1 (hd.2.1 i).2 hPpos`.

Establish `hmem` using `(pos_mem X.TT j i).1`. Establish `hbT : X.b' * (1 - be X C0) ≤ (X.bT (segPos X.TT j i) : ℝ)` using `(h.winB _ hmem).1`. Establish `hbe : be X C0 ≤ 1 / 2` using `by have := h.beLe; have := h.be0; have : 0 ≤ 18 * X.N1 * X.La C0 / X.k := by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb2 : X.b' / 2 ≤ ((X.seg C0 CE1 CE2 j).bTop i : ℝ)` using `by show X.b' / 2 ≤ (X.bT (segPos X.TT j i) : ℝ)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hP0 : (0 : ℝ) < ((X.seg C0 CE1 CE2 j).P X.p i : ℝ)` using `by exact_mod_cast hPpos`. Establish `h3 : X.b' / 2 / X.Q ≤ ((X.seg C0 CE1 CE2 j).bTop i : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ)`. Combine the equalities or inequalities in the displayed calculation. Establish `h4 : 2 * X.k ^ 3 ≤ X.b' / 2 / X.Q`.

Rewrite using `[div_div, le_div_iff₀ (by positivity)]; nlinarith`. Establish `hkr : ((X.m : ℝ) + 1) = X.k` using `rfl`. Use `show X.k ^ 3 ≤ (coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i : ℝ)`. Unfold `coarseA`. Use `show X.k ^ 3 ≤ ((((X.seg C0 CE1 CE2 j).bTop i - ∑ c, rz i c) / (X.seg C0 CE1 CE2 j).P X.p i : ℕ) : ℝ)`.

Rewrite `hgt` using `[hkr]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `i`. Establish `hPpos : 0 < (X.seg C0 CE1 CE2 j).P X.p i`. Unfold `SegData.P; exact pow_pos (by have := h.p5; omega) _`.

Establish `hPQ : ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) ≤ X.Q`. Establish `hl` using `h.levels j i`. Conclude with `le_trans hl.2.2.2.2 hl.2.2.2.1`. Establish `hgt` using `coarse_degree_gt_quotient (segATop X.TT X.aT j i) ((X.seg C0 CE1 CE2 j).P X.p i) (ry i) (fun c => (hd.1 i c).2) (hd.2.2 i).1 (hd.2.2 i).2 hPpos`. Establish `hmem` using `(pos_mem X.TT j i).1`.

Establish `haT : (X.a : ℝ) ≤ (segATop X.TT X.aT j i : ℝ)` using `(h.winA _ hmem).1`. Establish `hP0 : (0 : ℝ) < ((X.seg C0 CE1 CE2 j).P X.p i : ℝ)` using `by exact_mod_cast hPpos`. Establish `ha0 : (0 : ℝ) ≤ X.a` using `by positivity`. Establish `h3 : (X.a : ℝ) / X.Q ≤ (segATop X.TT X.aT j i : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ)`. Combine the equalities or inequalities in the displayed calculation.

Establish `h4 : 2 * X.k ^ 3 ≤ (X.a : ℝ) / X.Q`. Rewrite using `[le_div_iff₀ hQ0]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hkr : ((X.m : ℝ) + 1) = X.k` using `rfl`. Use `show X.k ^ 3 ≤ (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) i : ℝ)`.

Unfold `coarseC`. Use `show X.k ^ 3 ≤ (((segATop X.TT X.aT j i - ∑ c, ry i c) / (X.seg C0 CE1 CE2 j).P X.p i : ℕ) : ℝ)`. Rewrite `hgt` using `[hkr]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem coarse_degrees_large_of_std {C0 Cde CE1 CE2 : ℝ} {X : Loc} [NeZero X.m] (h : Std C0 Cde CE1 CE2 4 X) (j : Fin (numSeg X.TT))
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry)) (A : ℕ)
    (hA : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ)) :
    X.k ^ 3 ≤ (A : ℝ) ∧ (∀ i, X.k ^ 3 ≤ (clA C0 CE1 CE2 X j rz ry i : ℝ)) ∧
      (∀ i, X.k ^ 3 ≤ (clC C0 CE1 CE2 X j rz ry i : ℝ)) ∧ X.k ^ 2 ≤ (X.p : ℝ) ∧ 10 ≤ X.k ∧
      1 ≤ X.La C0 ∧ 4 * X.La C0 ≤ X.k := by
  have hk5 := h.k5
  have hk0 : 0 < X.k := by linarith
  have hY := h.Y1
  have hQ1 := h.Q1
  have hN2 := h.N2
  have hN1 := h.one_le_level_alt
  have hLa := h.La1
  have hb := h.bpos
  have hba := h.ba
  have hde := h.de6
  have hLaK := h.LaK

  have hK240 : 240 * (X.N1 : ℝ) * X.La C0 < X.k := by
    have h1 : 40 * (X.N1 : ℝ) * X.La C0 / X.k < 1 / 6 := lt_of_le_of_lt hLaK hde
    rw [div_lt_iff₀ hk0] at h1
    linarith
  have hNLa : 1 ≤ (X.N1 : ℝ) * X.La C0 := one_le_mul_of_one_le_of_one_le hN1 hLa
  have hk10 : 10 ≤ X.k := by nlinarith
  have hLa4 : 4 * X.La C0 ≤ X.k := by nlinarith
  have hkp : X.k ^ 2 ≤ (X.p : ℝ) := by
    have := h.pk
    have hY2 : 1 ≤ X.Y ^ 2 := one_le_pow₀ hY
    nlinarith [sq_nonneg X.k]

  have hb4 : 4 * X.k ^ 3 * X.Q ≤ X.b' := by
    have hHb := h.Hb
    have hNQY : X.Q ≤ X.N * X.Q ^ 4 * X.Y := by
      have q4 : X.Q ≤ X.Q ^ 4 := le_self_pow₀ hQ1 (by norm_num)
      have hN1' : (1 : ℝ) ≤ X.N := by linarith
      have : X.Q ^ 4 ≤ X.N * X.Q ^ 4 * X.Y := by
        have hq : 0 ≤ X.Q ^ 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hN1' hq]
      linarith
    have hk3 : 0 ≤ 4 * X.k ^ 3 := by positivity
    calc 4 * X.k ^ 3 * X.Q ≤ 4 * X.k ^ 3 * (X.N * X.Q ^ 4 * X.Y) := mul_le_mul_of_nonneg_left hNQY hk3
      _ = 4 * X.k ^ 3 * X.N * X.Q ^ 4 * X.Y := by ring
      _ ≤ X.b' := hHb
  have hQ0 : 0 < X.Q := by linarith
  have hk3 : X.k ≤ X.k ^ 3 := by nlinarith
  refine ⟨?_, ?_, ?_, hkp, hk10, hLa, hLa4⟩
  ·
    have hA0 := h.half_ratio_le_segment_base_of_std j
    have hfrac : X.N1 * X.La C0 / X.k ≤ 1 / 2 := by
      rw [div_le_iff₀ hk0]; nlinarith
    have hA0pos : 0 ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) := le_trans (by positivity) hA0
    have h1 : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) / 2 ≤ (A : ℝ) := by
      have : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 / 2) ≤
          ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) :=
        mul_le_mul_of_nonneg_left (by linarith) hA0pos
      linarith
    have h2 : X.k ^ 3 ≤ (X.a : ℝ) / (2 * X.Q) / 2 := by
      rw [div_div, le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  · intro i
    have hPpos : 0 < (X.seg C0 CE1 CE2 j).P X.p i := by
      unfold SegData.P; exact pow_pos (by have := h.p5; omega) _
    have hPQ : ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) ≤ X.Q := by
      have hl := h.levels j i
      exact le_trans hl.2.2.2.2 hl.2.2.2.1
    have hgt := coarse_degree_gt_quotient ((X.seg C0 CE1 CE2 j).bTop i) ((X.seg C0 CE1 CE2 j).P X.p i) (rz i)
      (fun c => (hd.1 i c).1) (hd.2.1 i).1 (hd.2.1 i).2 hPpos
    have hmem := (pos_mem X.TT j i).1
    have hbT : X.b' * (1 - be X C0) ≤ (X.bT (segPos X.TT j i) : ℝ) := (h.winB _ hmem).1
    have hbe : be X C0 ≤ 1 / 2 := by have := h.beLe; have := h.be0; have : 0 ≤ 18 * X.N1 * X.La C0 / X.k := by positivity
                                     linarith
    have hb2 : X.b' / 2 ≤ ((X.seg C0 CE1 CE2 j).bTop i : ℝ) := by
      show X.b' / 2 ≤ (X.bT (segPos X.TT j i) : ℝ)
      nlinarith
    have hP0 : (0 : ℝ) < ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) := by exact_mod_cast hPpos
    have h3 : X.b' / 2 / X.Q ≤ ((X.seg C0 CE1 CE2 j).bTop i : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) := by
      calc X.b' / 2 / X.Q ≤ X.b' / 2 / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) hP0 hPQ
        _ ≤ _ := div_le_div_of_nonneg_right hb2 hP0.le
    have h4 : 2 * X.k ^ 3 ≤ X.b' / 2 / X.Q := by
      rw [div_div, le_div_iff₀ (by positivity)]; nlinarith
    have hkr : ((X.m : ℝ) + 1) = X.k := rfl
    show X.k ^ 3 ≤ (coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i : ℝ)
    unfold coarseA
    show X.k ^ 3 ≤ ((((X.seg C0 CE1 CE2 j).bTop i - ∑ c, rz i c) / (X.seg C0 CE1 CE2 j).P X.p i : ℕ) : ℝ)
    rw [hkr] at hgt
    linarith
  · intro i
    have hPpos : 0 < (X.seg C0 CE1 CE2 j).P X.p i := by
      unfold SegData.P; exact pow_pos (by have := h.p5; omega) _
    have hPQ : ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) ≤ X.Q := by
      have hl := h.levels j i
      exact le_trans hl.2.2.2.2 hl.2.2.2.1
    have hgt := coarse_degree_gt_quotient (segATop X.TT X.aT j i) ((X.seg C0 CE1 CE2 j).P X.p i) (ry i)
      (fun c => (hd.1 i c).2) (hd.2.2 i).1 (hd.2.2 i).2 hPpos
    have hmem := (pos_mem X.TT j i).1
    have haT : (X.a : ℝ) ≤ (segATop X.TT X.aT j i : ℝ) := (h.winA _ hmem).1
    have hP0 : (0 : ℝ) < ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) := by exact_mod_cast hPpos
    have ha0 : (0 : ℝ) ≤ X.a := by positivity
    have h3 : (X.a : ℝ) / X.Q ≤ (segATop X.TT X.aT j i : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) := by
      calc (X.a : ℝ) / X.Q ≤ (X.a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) :=
            div_le_div_of_nonneg_left ha0 hP0 hPQ
        _ ≤ _ := div_le_div_of_nonneg_right haT hP0.le
    have h4 : 2 * X.k ^ 3 ≤ (X.a : ℝ) / X.Q := by
      rw [le_div_iff₀ hQ0]; nlinarith
    have hkr : ((X.m : ℝ) + 1) = X.k := rfl
    show X.k ^ 3 ≤ (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) i : ℝ)
    unfold coarseC
    show X.k ^ 3 ≤ (((segATop X.TT X.aT j i - ∑ c, ry i c) / (X.seg C0 CE1 CE2 j).P X.p i : ℕ) : ℝ)
    rw [hkr] at hgt
    linarith

/- English proof (translation)
The claim follows from `TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 4) fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 => fun X _ hD hI hc j rz ry hd A hA => coarse_degrees_large_of_std (std_of hCc hC0 h1 h2 (by norm_num : (1 : ℝ) …`.
-/
theorem coarse_degrees_large_holds : CoarseDegreesLargeBeyond :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 4)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
      fun X _ hD hI hc j rz ry hd A hA =>
        coarse_degrees_large_of_std (std_of hCc hC0 h1 h2 (by norm_num : (1 : ℝ) ≤ 4) t1 t2 t3 t4 t5 hD hI hc) j rz ry hd A hA

section PFA

variable {s r A : ℕ} {Ai Ci : Fin s → ℕ} {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ} {lam : Fin r → ℤ}

/- English proof (translation)
Establish `hr : 0 < r` using `Nat.pos_of_ne_zero (NeZero.ne r)`. Unfold `pairRho wbK`. Rewrite using `[finPos_eq (2 * s + 1) (2 * i.val + 2) (by omega), dif_pos ⟨by omega, hr⟩]`. Both sides reduce to the same expression.
-/
theorem pfa_rho_eq [NeZero r] (i : Fin s) : pairRho mu i.val = wbK mu (2 * i.val + 2) 0 := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  unfold pairRho wbK
  rw [finPos_eq (2 * s + 1) (2 * i.val + 2) (by omega), dif_pos ⟨by omega, hr⟩]
  rfl

/- English proof (translation)
Break down `Nat.eq_zero_or_pos i with h0 | h0` into its components or cases. Substitute `h0` using the available equality. Rewrite using `[wb_one hP 0]`. Conclude with `(wb_shape hP hr i hi).1 0 h0`.
-/
theorem pfa_odd_nonneg (hP : IsPair A Ai Ci mu lam) (hr : 2 * s + 1 ≤ r) (i : ℕ) (hi : i ≤ s) :
    0 ≤ wbK mu (2 * i + 1) 0 := by
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0; rw [wb_one hP 0]
  · exact (wb_shape hP hr i hi).1 0 h0

/- English proof (translation)
Rewrite using `[pfa_rho_eq]`. Establish `hr0 : 0 < r` using `Nat.pos_of_ne_zero (NeZero.ne r)`. Establish `h1` using `(wb_vstep hP (2 * i.val + 1) (by omega) (Or.inr (by omega))).1 0 hr0`. Establish `h2` using `pfa_odd_nonneg hP hr i.val (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pfa_rho_nonneg [NeZero r] (hP : IsPair A Ai Ci mu lam) (hr : 2 * s + 1 ≤ r) (i : Fin s) :
    0 ≤ pairRho mu i.val := by
  rw [pfa_rho_eq]
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have h1 := (wb_vstep hP (2 * i.val + 1) (by omega) (Or.inr (by omega))).1 0 hr0
  have h2 := pfa_odd_nonneg hP hr i.val (by omega)
  linarith

/- English proof (translation)
Establish `key : ∀ l, l ≤ s → 0 ≤ pairC mu l`. Introduce `l hl`. Break down `Nat.eq_zero_or_pos l with h0 | h0` into its components or cases. Substitute `h0` using the available equality. Rewrite using `[pairC_zero hP.1]`.

Conclude with `Int.natCast_nonneg _`. Take `⟨i, rfl⟩ : ∃ i, l = i + 1` from `⟨l - 1, by omega⟩`. Establish `h1` using `(pf_rho_le_c hP.1 (⟨i, by omega⟩ : Fin s)).2`. Establish `h2` using `pfa_rho_nonneg hP hr (⟨i, by omega⟩ : Fin s)`. Conclude with `le_trans h2 h1`.

Break down `le_or_gt l s with hl | hl` into its components or cases. Conclude with `key l hl`. Establish `e : pairC mu l = pairC mu s`. Unfold `pairC`. Use `congr 1`.

Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [finPos]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e]`. Conclude with `key s le_rfl`.
-/
theorem pfa_c_nonneg [NeZero r] (hP : IsPair A Ai Ci mu lam) (hr : 2 * s + 1 ≤ r) (l : ℕ) : 0 ≤ pairC mu l := by
  have key : ∀ l, l ≤ s → 0 ≤ pairC mu l := by
    intro l hl
    rcases Nat.eq_zero_or_pos l with h0 | h0
    · subst h0; rw [pairC_zero hP.1]; exact Int.natCast_nonneg _
    · obtain ⟨i, rfl⟩ : ∃ i, l = i + 1 := ⟨l - 1, by omega⟩
      have h1 := (pf_rho_le_c hP.1 (⟨i, by omega⟩ : Fin s)).2
      have h2 := pfa_rho_nonneg hP hr (⟨i, by omega⟩ : Fin s)
      exact le_trans h2 h1
  rcases le_or_gt l s with hl | hl
  · exact key l hl
  · have e : pairC mu l = pairC mu s := by
      unfold pairC
      congr 1
      apply Fin.ext
      simp only [finPos]
      omega
    rw [e]; exact key s le_rfl

end PFA

section PFB

variable {s r A : ℕ} {Ai Ci : Fin s → ℕ} {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ} {lam : Fin r → ℤ}

/- English proof (translation)
Establish `h1` using `pf_prev_le hP.1 i.val (by omega)`. Establish `h2 : (∑ x : Fin s, if x.val < i.val then pairW mu x.val else 0) ≤ ∑ x : Fin s, if x.val < i.val then (Ai x : ℤ) else 0` using `Finset.sum_le_sum fun x _ => by split_ifs`. Conclude with `(pair_top hP.1 x).2.2.2.1`. Conclude with `le_rfl`. Establish `h3` using `le_trans h1 h2`.

Establish `h4` using `(Int.cast_le (R := ℝ)).2 h3`. Move the coercions through the operations in `at h4`. Use `h4 using 2 with x` and compare the differences between its conclusion and the goal.
-/
theorem pfa_prev_real [NeZero r] (hP : IsPair A Ai Ci mu lam) (i : Fin s) :
    ((mu ⟨2 * i.val + 1, by omega⟩ (0 : Fin r).succ : ℤ) : ℝ) ≤
      ∑ l : Fin s, if l.val < i.val then (Ai l : ℝ) else 0 := by
  have h1 := pf_prev_le hP.1 i.val (by omega)
  have h2 : (∑ x : Fin s, if x.val < i.val then pairW mu x.val else 0) ≤
      ∑ x : Fin s, if x.val < i.val then (Ai x : ℤ) else 0 :=
    Finset.sum_le_sum fun x _ => by
      split_ifs
      · exact (pair_top hP.1 x).2.2.2.1
      · exact le_rfl
  have h3 := le_trans h1 h2
  have h4 := (Int.cast_le (R := ℝ)).2 h3
  push_cast at h4
  convert h4 using 2 with x

/- English proof (translation)
Establish `h1` using `pf_rho_le hP.1 i`. Establish `h2` using `pfa_prev_real hP i`. Establish `h3 : ((pairW mu i.val : ℤ) : ℝ) ≤ (Ai i : ℝ)` using `by exact_mod_cast (pair_top hP.1 i).2.2.2.1`. Establish `h4` using `(Int.cast_le (R := ℝ)).2 h1`. Move the coercions through the operations in `at h4`.

Establish `h5` using `hN i`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pfa_rho_up [NeZero r] (hP : IsPair A Ai Ci mu lam) (q : ℝ)
    (hN : ∀ i : Fin s, (∑ l : Fin s, if l.val < i.val then (Ai l : ℝ) else 0) ≤ q * Ai i) (i : Fin s) :
    ((pairRho mu i.val : ℤ) : ℝ) ≤ (Ai i : ℝ) * (1 + q) := by
  have h1 := pf_rho_le hP.1 i
  have h2 := pfa_prev_real hP i
  have h3 : ((pairW mu i.val : ℤ) : ℝ) ≤ (Ai i : ℝ) := by exact_mod_cast (pair_top hP.1 i).2.2.2.1
  have h4 := (Int.cast_le (R := ℝ)).2 h1
  push_cast at h4
  have h5 := hN i
  nlinarith

/- English proof (translation)
Establish `h1` using `pf_u_ge hP.1 i`. Establish `h2` using `pfa_prev_real hP i`. Establish `h3 : (0 : ℝ) ≤ ((pairSg mu Ai i : ℤ) : ℝ)` using `by exact_mod_cast (pair_top hP.1 i).2.2.2.2.1`. Establish `h4` using `(Int.cast_le (R := ℝ)).2 h1`. Move the coercions through the operations in `at h4 ⊢`.

Establish `h5` using `hN i`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pfa_u_low [NeZero r] (hP : IsPair A Ai Ci mu lam) (q : ℝ)
    (hN : ∀ i : Fin s, (∑ l : Fin s, if l.val < i.val then (Ai l : ℝ) else 0) ≤ q * Ai i) (i : Fin s) :
    -(q * (Ai i : ℝ)) ≤ ((pairO mu Ai i - pairRho mu i.val : ℤ) : ℝ) := by
  have h1 := pf_u_ge hP.1 i
  have h2 := pfa_prev_real hP i
  have h3 : (0 : ℝ) ≤ ((pairSg mu Ai i : ℤ) : ℝ) := by exact_mod_cast (pair_top hP.1 i).2.2.2.2.1
  have h4 := (Int.cast_le (R := ℝ)).2 h1
  push_cast at h4 ⊢
  have h5 := hN i
  linarith

/- English proof (translation)
Establish `hr0 : 0 < r` using `Nat.pos_of_ne_zero (NeZero.ne r)`. Take `⟨i1, i2⟩` from `hP.2 ⟨0, hr0⟩`. Use `⟨le_trans ?_ i1, ?_⟩` and prove the remaining obligations. Establish `h` using `pfa_odd_nonneg hP hr s le_rfl`. Establish `e : wbK mu (2 * s + 1) 0 = mu (Fin.last _) (Fin.succ ⟨0, hr0⟩)` using `wb_last 0 hr0`.

Rewrite `h` using `[e]`. Conclude with `h`. Establish `e : pairC mu s = mu (Fin.last _) (Fin.castSucc ⟨0, hr0⟩)`. Unfold `pairC; rw [finPos_eq (2 * s + 1) (2 * s + 1) (by omega)]; rfl`. Rewrite using `[e]`.

Conclude with `i2`.
-/
theorem pair_first_weight_bounds (hP : IsPair A Ai Ci mu lam) (hr : 2 * s + 1 ≤ r) [NeZero r] :
    0 ≤ lam ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩ ∧ lam ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩ ≤ pairC mu s := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  obtain ⟨i1, i2⟩ := hP.2 ⟨0, hr0⟩
  refine ⟨le_trans ?_ i1, ?_⟩
  · have h := pfa_odd_nonneg hP hr s le_rfl
    have e : wbK mu (2 * s + 1) 0 = mu (Fin.last _) (Fin.succ ⟨0, hr0⟩) := wb_last 0 hr0
    rw [e] at h; exact h
  · have e : pairC mu s = mu (Fin.last _) (Fin.castSucc ⟨0, hr0⟩) := by
      unfold pairC; rw [finPos_eq (2 * s + 1) (2 * s + 1) (by omega)]; rfl
    rw [e]; exact i2

/- English proof (translation)
Unfold `pairN`. Rewrite using `[dif_pos (by omega)]`. Establish `hi` using `i.2`. Take `⟨i1, i2⟩` from `hP.2 ⟨r - s + i.val, by omega⟩`. Establish `hsh` using `wb_shape hP hr s le_rfl`.

Establish `e : mu (Fin.last _) (Fin.castSucc ⟨r - s + i.val, by omega⟩) = wbK mu (2 * s + 1) (r - s + i.val - 1)`. Rewrite using `[wb_last (r - s + i.val - 1) (by omega)]`. Use `congr 1`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [Fin.coe_castSucc]`.

Use linear arithmetic over natural numbers and integers. Establish `hle : wbK mu (2 * s + 1) (r - s + i.val - 1) ≤ 0`. Break down `Nat.eq_zero_or_pos i.val with h0 | h0` into its components or cases. Rewrite using `[hsh.2.1 _ (by omega) (by omega)]`. Conclude with `hsh.2.2 _ (by omega)`.

Rewrite `i2` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pfa_n_nonneg (hP : IsPair A Ai Ci mu lam) (hr : 2 * s + 1 ≤ r) (i : Fin s) :
    0 ≤ pairN (s := s) lam i.val := by
  unfold pairN
  rw [dif_pos (by omega)]
  have hi := i.2
  obtain ⟨i1, i2⟩ := hP.2 ⟨r - s + i.val, by omega⟩
  have hsh := wb_shape hP hr s le_rfl
  have e : mu (Fin.last _) (Fin.castSucc ⟨r - s + i.val, by omega⟩) = wbK mu (2 * s + 1) (r - s + i.val - 1) := by
    rw [wb_last (r - s + i.val - 1) (by omega)]
    congr 1
    apply Fin.ext
    simp only [Fin.coe_castSucc]
    omega
  have hle : wbK mu (2 * s + 1) (r - s + i.val - 1) ≤ 0 := by
    rcases Nat.eq_zero_or_pos i.val with h0 | h0
    · rw [hsh.2.1 _ (by omega) (by omega)]
    · exact hsh.2.2 _ (by omega)
  rw [e] at i2
  linarith

end PFB

def NUpAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) →
        ∀ (mu : Fin (2 * segS X.TT j + 1 + 1) → Fin (X.m + 1) → ℤ) (lam : Fin X.m → ℤ),
          IsPair A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
          ∀ i : Fin (segS X.TT j),
            ((pairN (s := segS X.TT j) lam i : ℤ) : ℝ) ≤ (clC C0 CE1 CE2 X j rz ry i : ℝ) * (1 + 4 / (X.p : ℝ) ^ 2)

def RestNUp : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => NUpAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

/- English proof (translation)
Establish `hstd : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X` using `TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1) fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 => fun X hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc`. Use `TransportedAlt.mono ?_ (hstd.and h)` and prove the remaining obligations. Introduce and unpack `C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc ⟨hS, hN⟩ X _ hD hI hc j rz ry hd A hA1 hA2 mu lam hP`. Establish `St` using `hS X hD hI hc`. Establish `hr : 2 * segS X.TT j + 1 ≤ X.m`.

Establish `h1` using `(St.segB j).2`. Establish `h2` using `St.N1k`. Establish `h3 : (2 * (X.N1 : ℝ) + 3) ≤ (X.m : ℝ) + 1` using `h2`. Establish `h4 : 2 * X.N1 + 2 ≤ X.m` using `by exact_mod_cast (by linarith : (2 * (X.N1 : ℝ) + 2) ≤ (X.m : ℝ))`. Use linear arithmetic over natural numbers and integers.

Establish `hN4` using `coarse_degree_prefix_sum St le_rfl j rz ry hd`. Establish `hNq : ∀ i : Fin (segS X.TT j), (∑ l : Fin (segS X.TT j), if l.val < i.val then (clA C0 CE1 CE2 X j rz ry l : ℝ) else 0) ≤ 4 / (X.p : ℝ) ^ 2 * (clA C0 CE1 CE2 X j rz ry i : ℝ)` using `fun i => by`. Use `hN4 i` as an intermediate fact. Rewrite `*` using `[mul_comm, mul_div_assoc']`. Combine the linear relations using `[this, show 4 * (clA C0 CE1 CE2 X j rz ry i : ℝ) / (X.p : ℝ) ^ 2 = (clA C0 CE1 CE2 X j rz ry i : ℝ) * 4 / (X.p : ℝ) ^ 2 by ring]`.

Establish `hl0` using `pair_first_weight_bounds hP hr`. Establish `e0 : (0 : Fin X.m) = ⟨0, Nat.pos_of_ne_zero (NeZero.ne X.m)⟩` using `Fin.ext (by simp)`. Use `⟨pairC_zero hP.1, fun l => pfa_c_nonneg hP hr l, fun i => ⟨pfa_rho_nonneg hP hr i, (pf_rho_le_c hP.1 i).1, pfa_rho_up hP _ hNq i, ?_⟩, by rw [e0]; exact hl0.1, by rw [e0]; exact hl0.2, fun i => ⟨pfa_n_nonneg hP hr i, hN X hD hI hc j rz ry hd A hA1 hA2 mu lam hP i⟩⟩` and prove the remaining obligations. Use `pfa_u_low hP _ hNq i` as an intermediate fact. Establish `e : 4 * (clA C0 CE1 CE2 X j rz ry i : ℝ) / (X.p : ℝ) ^ 2 = 4 / (X.p : ℝ) ^ 2 * (clA C0 CE1 CE2 X j rz ry i : ℝ)` using `by ring`.

Rewrite using `[e]`. Conclude with `this`.
-/
theorem restPairFacts_of (h : RestNUp) : RestPairFacts := by
  have hstd : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc =>
      ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X :=
    TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
      fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
        fun X hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc
  refine TransportedAlt.mono ?_ (hstd.and h)
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc ⟨hS, hN⟩ X _ hD hI hc j rz ry hd A hA1 hA2 mu lam hP
  have St := hS X hD hI hc
  have hr : 2 * segS X.TT j + 1 ≤ X.m := by
    have h1 := (St.segB j).2
    have h2 := St.N1k
    have h3 : (2 * (X.N1 : ℝ) + 3) ≤ (X.m : ℝ) + 1 := h2
    have h4 : 2 * X.N1 + 2 ≤ X.m := by exact_mod_cast (by linarith : (2 * (X.N1 : ℝ) + 2) ≤ (X.m : ℝ))
    omega
  have hN4 := coarse_degree_prefix_sum St le_rfl j rz ry hd
  have hNq : ∀ i : Fin (segS X.TT j), (∑ l : Fin (segS X.TT j), if l.val < i.val then (clA C0 CE1 CE2 X j rz ry l : ℝ) else 0) ≤
      4 / (X.p : ℝ) ^ 2 * (clA C0 CE1 CE2 X j rz ry i : ℝ) := fun i => by
    have := hN4 i
    rw [mul_comm, mul_div_assoc'] at *
    linarith [this, show 4 * (clA C0 CE1 CE2 X j rz ry i : ℝ) / (X.p : ℝ) ^ 2 =
      (clA C0 CE1 CE2 X j rz ry i : ℝ) * 4 / (X.p : ℝ) ^ 2 by ring]
  have hl0 := pair_first_weight_bounds hP hr
  have e0 : (0 : Fin X.m) = ⟨0, Nat.pos_of_ne_zero (NeZero.ne X.m)⟩ := Fin.ext (by simp)
  refine ⟨pairC_zero hP.1, fun l => pfa_c_nonneg hP hr l, fun i => ⟨pfa_rho_nonneg hP hr i, (pf_rho_le_c hP.1 i).1,
    pfa_rho_up hP _ hNq i, ?_⟩, by rw [e0]; exact hl0.1, by rw [e0]; exact hl0.2,
    fun i => ⟨pfa_n_nonneg hP hr i, hN X hD hI hc j rz ry hd A hA1 hA2 mu lam hP i⟩⟩
  have := pfa_u_low hP _ hNq i
  have e : 4 * (clA C0 CE1 CE2 X j rz ry i : ℝ) / (X.p : ℝ) ^ 2 = 4 / (X.p : ℝ) ^ 2 * (clA C0 CE1 CE2 X j rz ry i : ℝ) := by ring
  rw [e]; exact this

end Formalism.MainNotions.ColumnSystems.Pf
