import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FourDepthLtConductorOfBounds
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MeanDefs

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def Cst.TM (K : Cst) : ℝ := max K.TLP (max (4 * K.CH + 1) (2 * K.Cm + 24))

/- English proof (translation)
The claim follows from `lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 108) (le_trans (le_max_left _ _) (le_max_left _ _))) (le_max_left _ _)`.
-/
theorem TM_pos (K : Cst) : 0 < K.TM :=
  lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 108) (le_trans (le_max_left _ _) (le_max_left _ _)))
    (le_max_left _ _)

/- English proof (translation)
Use `mul_le_mul B.hp25 B.hb8 (by norm_num) (by linarith [B.hp25])` as an intermediate fact. Combine the linear relations using `[B.hpa]`.
-/
theorem two_hundred_le_radius {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) : (200 : ℝ) ≤ X.ar := by
  have := mul_le_mul B.hp25 B.hb8 (by norm_num) (by linarith [B.hp25])
  linarith [B.hpa]

/- English proof (translation)
Establish `h200` using `two_hundred_le_radius B`. Establish `har : 0 < X.ar` using `by linarith`. Establish `ha : (0 : ℝ) < X.a` using `by linarith [B.haa]`. Use `⟨Real.log_le_log har B.haa, ?_⟩` and prove the remaining obligations. Establish `h1 : Real.log ((X.a : ℝ) / X.ar) = Real.log X.a - Real.log X.ar` using `Real.log_div ha.ne' har.ne'`.

Establish `h2` using `Real.log_le_sub_one_of_pos (div_pos ha har)`. Establish `h3 : (X.a : ℝ) / X.ar - 1 ≤ 1 / 200`. Establish `: (X.a : ℝ) / X.ar ≤ 1 + 1 / 200`. Rewrite using `[div_le_iff₀ har]`. Combine the linear relations using `[B.haa1]`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_round {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) :
    Real.log X.ar ≤ Real.log X.a ∧ Real.log X.a ≤ Real.log X.ar + 1 / 200 := by
  have h200 := two_hundred_le_radius B
  have har : 0 < X.ar := by linarith
  have ha : (0 : ℝ) < X.a := by linarith [B.haa]
  refine ⟨Real.log_le_log har B.haa, ?_⟩
  have h1 : Real.log ((X.a : ℝ) / X.ar) = Real.log X.a - Real.log X.ar := Real.log_div ha.ne' har.ne'
  have h2 := Real.log_le_sub_one_of_pos (div_pos ha har)
  have h3 : (X.a : ℝ) / X.ar - 1 ≤ 1 / 200 := by
    have : (X.a : ℝ) / X.ar ≤ 1 + 1 / 200 := by
      rw [div_le_iff₀ har]
      linarith [B.haa1]
    linarith
  linarith

/- English proof (translation)
Take `⟨h1, h2⟩` from `log_round B`. Establish `hl` using `B.hlog1`. Establish `hC0 : 0 < K.C₀` using `hK.1`. Establish `hcn : 0 ≤ K.C₀ * (X.N₁ : ℝ) ^ 2` using `by positivity`. Unfold `LaI`.

Use `⟨mul_le_mul_of_nonneg_left h1 hcn, ?_, ?_⟩` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left (by linarith : Real.log X.a ≤ 2 * Real.log X.ar) hcn` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsq : Real.log X.a * Real.log X.a ≤ 2 * (Real.log X.ar * Real.log X.ar)`. Establish `a1 : Real.log X.a ≤ (1 + 1 / 200) * Real.log X.ar` using `by linarith`.

Establish `a0 : 0 ≤ Real.log X.a` using `by linarith`. Establish `a2` using `mul_le_mul a1 a1 a0 (by linarith)`. Establish `a3 : 0 ≤ Real.log X.ar * Real.log X.ar` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Use `mul_le_mul_of_nonneg_left hsq hcn` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem La_round {K : Cst} (hK : K.Pos) {CH : ℝ} {X : Dat} (B : Base K CH X) :
    LaI K.C₀ X.N₁ X.ar ≤ LaI K.C₀ X.N₁ X.a ∧ LaI K.C₀ X.N₁ X.a ≤ 2 * LaI K.C₀ X.N₁ X.ar ∧
      LaI K.C₀ X.N₁ X.a * Real.log X.a ≤ 2 * (LaI K.C₀ X.N₁ X.ar * Real.log X.ar) := by
  obtain ⟨h1, h2⟩ := log_round B
  have hl := B.hlog1
  have hC0 : 0 < K.C₀ := hK.1
  have hcn : 0 ≤ K.C₀ * (X.N₁ : ℝ) ^ 2 := by positivity
  unfold LaI
  refine ⟨mul_le_mul_of_nonneg_left h1 hcn, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left (by linarith : Real.log X.a ≤ 2 * Real.log X.ar) hcn
    linarith
  · have hsq : Real.log X.a * Real.log X.a ≤ 2 * (Real.log X.ar * Real.log X.ar) := by
      have a1 : Real.log X.a ≤ (1 + 1 / 200) * Real.log X.ar := by linarith
      have a0 : 0 ≤ Real.log X.a := by linarith
      have a2 := mul_le_mul a1 a1 a0 (by linarith)
      have a3 : 0 ≤ Real.log X.ar * Real.log X.ar := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_left hsq hcn
    calc K.C₀ * (X.N₁ : ℝ) ^ 2 * Real.log X.a * Real.log X.a
        = K.C₀ * (X.N₁ : ℝ) ^ 2 * (Real.log X.a * Real.log X.a) := by ring
      _ ≤ K.C₀ * (X.N₁ : ℝ) ^ 2 * (2 * (Real.log X.ar * Real.log X.ar)) := this
      _ = _ := by ring

/- English proof (translation)
Establish `hc : 0 ≤ Yb * N * b' / k` using `by positivity`. Use `mul_le_mul_of_nonneg_left (by linarith : La' / 2 ≤ La) hc` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.
-/
theorem r12 (Yb N La La' b' k w : ℝ) (hYb : 0 ≤ Yb) (hN : 0 ≤ N) (hb : 0 ≤ b') (hk : 0 < k) (h2 : La' ≤ 2 * La)
    (h : Yb * N * La * b' / k ≤ w) : Yb / 2 * N * La' * b' / k ≤ w := by
  have hc : 0 ≤ Yb * N * b' / k := by positivity
  have := mul_le_mul_of_nonneg_left (by linarith : La' / 2 ≤ La) hc
  calc Yb / 2 * N * La' * b' / k = Yb * N * b' / k * (La' / 2) := by ring
    _ ≤ Yb * N * b' / k * La := this
    _ = Yb * N * La * b' / k := by ring
    _ ≤ w := h

/- English proof (translation)
Establish `hc : 0 ≤ Yb * N` using `by positivity`. Use `mul_le_mul_of_nonneg_left h2 hc` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.
-/
theorem r15 (Yb N La La' k : ℝ) (hYb : 0 ≤ Yb) (hN : 0 ≤ N) (h2 : La' ≤ 2 * La) (h : 2 * Yb * N * La < k) :
    2 * (Yb / 2) * N * La' < k := by
  have hc : 0 ≤ Yb * N := by positivity
  have := mul_le_mul_of_nonneg_left h2 hc
  calc 2 * (Yb / 2) * N * La' = Yb * N * La' := by ring
    _ ≤ Yb * N * (2 * La) := this
    _ = 2 * Yb * N * La := by ring
    _ < k := h

/- English proof (translation)
Establish `hc : 0 ≤ k * Y ^ 2 * Yb * N / 2` using `by positivity`. Use `mul_le_mul_of_nonneg_left h2 hc` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.
-/
theorem r16 (k Y Yb N La La' l l' ar a' b' : ℝ) (hk : 0 ≤ k) (hY : 0 ≤ Y) (hYb : 0 ≤ Yb) (hN : 0 ≤ N) (hb : 0 < b')
    (ha : ar ≤ a') (h2 : La' * l' ≤ 2 * (La * l)) (h : k * Y ^ 2 * Yb * N * La * l ≤ ar / b') :
    k * Y ^ 2 * (Yb / 2) * N * La' * l' ≤ a' / b' := by
  have hc : 0 ≤ k * Y ^ 2 * Yb * N / 2 := by positivity
  have := mul_le_mul_of_nonneg_left h2 hc
  calc k * Y ^ 2 * (Yb / 2) * N * La' * l' = k * Y ^ 2 * Yb * N / 2 * (La' * l') := by ring
    _ ≤ k * Y ^ 2 * Yb * N / 2 * (2 * (La * l)) := this
    _ = k * Y ^ 2 * Yb * N * La * l := by ring
    _ ≤ ar / b' := h
    _ ≤ a' / b' := div_le_div_of_nonneg_right ha hb.le

/- English proof (translation)
Establish `h1 : CH1 * N1 * La' + 1 ≤ CH * N1 * La`. Establish `a1 : CH1 * N1 * La' ≤ CH1 * N1 * (2 * La)` using `mul_le_mul_of_nonneg_left h2 (by positivity)`. Establish `a2 : 1 ≤ N1 * La` using `one_le_mul_of_one_le_of_one_le hN1 hLa`. Establish `a3 : (2 * CH1 + 1) * (N1 * La) ≤ CH * (N1 * La)` using `mul_le_mul_of_nonneg_right hCH (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.

Use `div_le_div_of_nonneg_right h1 hk.le` as an intermediate fact. Establish `e : (CH1 * N1 * La' + 1) / k = CH1 * N1 * La' / k + 1 / k` using `add_div _ _ _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rde (CH CH1 N1 La La' k r : ℝ) (hCH1 : 0 ≤ CH1) (hCH : 2 * CH1 + 1 ≤ CH) (hN1 : 1 ≤ N1) (hLa : 1 ≤ La)
    (h2 : La' ≤ 2 * La) (hk : 0 < k) : CH1 * N1 * La' / k + r + 1 / k ≤ CH * N1 * La / k + r := by
  have h1 : CH1 * N1 * La' + 1 ≤ CH * N1 * La := by
    have a1 : CH1 * N1 * La' ≤ CH1 * N1 * (2 * La) := mul_le_mul_of_nonneg_left h2 (by positivity)
    have a2 : 1 ≤ N1 * La := one_le_mul_of_one_le_of_one_le hN1 hLa
    have a3 : (2 * CH1 + 1) * (N1 * La) ≤ CH * (N1 * La) := mul_le_mul_of_nonneg_right hCH (by linarith)
    nlinarith
  have := div_le_div_of_nonneg_right h1 hk.le
  have e : (CH1 * N1 * La' + 1) / k = CH1 * N1 * La' / k + 1 / k := add_div _ _ _
  linarith

/- English proof (translation)
Establish `har : 0 < ar` using `lt_of_lt_of_le hk hka`. Establish `hk1 : 0 < 1 / k` using `by positivity`. Establish `hab : ar / b' ≤ a' / b'` using `div_le_div_of_nonneg_right ha hb.le`. Establish `hab0 : 0 ≤ ar / b'` using `by positivity`. Prove the components needed by the constructor for the conclusion.

Use `le_trans ?_ h.1` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `le_trans h.2 ?_` and prove the remaining obligations. Establish `h1 : a' * (1 + 2 * de') ≤ ar * (1 + 2 * de)`. Establish `a1 : a' * (1 + 2 * de') ≤ (ar + 1) * (1 + 2 * de')` using `mul_le_mul_of_nonneg_right ha1 (by linarith)`.

Establish `a2 : ar * (1 + 2 * de' + 2 * (1 / k)) ≤ ar * (1 + 2 * de)` using `mul_le_mul_of_nonneg_left (by linarith) har.le`. Establish `a3 : 1 ≤ ar * (1 / k)`. Rewrite using `[mul_one_div, le_div_iff₀ hk]`. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem rband (ar a' b' de de' k x : ℝ) (hb : 0 < b') (hk : 0 < k) (hka : k ≤ ar) (ha : ar ≤ a') (ha1 : a' ≤ ar + 1)
    (hde0 : 0 ≤ de') (hde6 : de' < 1 / 6) (hde : de' + 1 / k ≤ de)
    (h : a' / b' * (1 - 2 * de') ≤ x ∧ x ≤ a' / b' * (1 + 2 * de')) :
    ar / b' * (1 - 2 * de) ≤ x ∧ x ≤ ar / b' * (1 + 2 * de) := by
  have har : 0 < ar := lt_of_lt_of_le hk hka
  have hk1 : 0 < 1 / k := by positivity
  have hab : ar / b' ≤ a' / b' := div_le_div_of_nonneg_right ha hb.le
  have hab0 : 0 ≤ ar / b' := by positivity
  constructor
  · refine le_trans ?_ h.1
    calc ar / b' * (1 - 2 * de) ≤ ar / b' * (1 - 2 * de') := mul_le_mul_of_nonneg_left (by linarith) hab0
      _ ≤ a' / b' * (1 - 2 * de') := mul_le_mul_of_nonneg_right hab (by linarith)
  · refine le_trans h.2 ?_
    have h1 : a' * (1 + 2 * de') ≤ ar * (1 + 2 * de) := by
      have a1 : a' * (1 + 2 * de') ≤ (ar + 1) * (1 + 2 * de') := mul_le_mul_of_nonneg_right ha1 (by linarith)
      have a2 : ar * (1 + 2 * de' + 2 * (1 / k)) ≤ ar * (1 + 2 * de) := mul_le_mul_of_nonneg_left (by linarith) har.le
      have a3 : 1 ≤ ar * (1 / k) := by
        rw [mul_one_div, le_div_iff₀ hk]
        linarith
      nlinarith
    calc a' / b' * (1 + 2 * de') = a' * (1 + 2 * de') / b' := by ring
      _ ≤ ar * (1 + 2 * de) / b' := div_le_div_of_nonneg_right h1 hb.le
      _ = _ := by ring

/- English proof (translation)
Establish `a1 : La' ^ 2 ≤ (2 * La) ^ 2` using `pow_le_pow_left₀ hLa0 h2 2`. Establish `a2 : CH1 * N * La' ^ 2 ≤ CH1 * N * (2 * La) ^ 2` using `mul_le_mul_of_nonneg_left a1 (by positivity)`. Establish `a3 : 4 * CH1 * (N * La ^ 2) ≤ CH * (N * La ^ 2)` using `mul_le_mul_of_nonneg_right hCH (by positivity)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem r19 (CH CH1 N La La' k : ℝ) (hCH1 : 0 ≤ CH1) (hCH : 4 * CH1 ≤ CH) (hN : 0 ≤ N) (hLa0 : 0 ≤ La')
    (h2 : La' ≤ 2 * La) (h : CH * N * La ^ 2 ≤ k) : CH1 * N * La' ^ 2 ≤ k := by
  have a1 : La' ^ 2 ≤ (2 * La) ^ 2 := pow_le_pow_left₀ hLa0 h2 2
  have a2 : CH1 * N * La' ^ 2 ≤ CH1 * N * (2 * La) ^ 2 := mul_le_mul_of_nonneg_left a1 (by positivity)
  have a3 : 4 * CH1 * (N * La ^ 2) ≤ CH * (N * La ^ 2) := mul_le_mul_of_nonneg_right hCH (by positivity)
  calc CH1 * N * La' ^ 2 ≤ CH1 * N * (2 * La) ^ 2 := a2
    _ = 4 * CH1 * (N * La ^ 2) := by ring
    _ ≤ CH * (N * La ^ 2) := a3
    _ = CH * N * La ^ 2 := by ring
    _ ≤ k := h

/- English proof (translation)
Establish `a1 : CH1 * G * L' ≤ CH1 * G * (2 * L)` using `mul_le_mul_of_nonneg_left h2 (by positivity)`. Establish `a2 : 2 * CH1 * (G * L) ≤ CH * (G * L)` using `mul_le_mul_of_nonneg_right hCH (by positivity)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem r22 (CH CH1 G L L' Dp : ℝ) (hCH1 : 0 ≤ CH1) (hCH : 2 * CH1 ≤ CH) (hG : 0 ≤ G) (hL : 0 ≤ L) (h2 : L' ≤ 2 * L)
    (h : CH * G * L ≤ Dp) : CH1 * G * L' ≤ Dp := by
  have a1 : CH1 * G * L' ≤ CH1 * G * (2 * L) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have a2 : 2 * CH1 * (G * L) ≤ CH * (G * L) := mul_le_mul_of_nonneg_right hCH (by positivity)
  calc CH1 * G * L' ≤ CH1 * G * (2 * L) := a1
    _ = 2 * CH1 * (G * L) := by ring
    _ ≤ CH * (G * L) := a2
    _ = CH * G * L := by ring
    _ ≤ Dp := h

/- English proof (translation)
Take `⟨hY, hp, hev, hseg2, hgap, hN1, hm, hLa8, hb, hbl, hbu, hIb1, hIb2, hYb, hk2, hab, hde, hpab, hkLa, hband, hccl, hD, hcs, hsize⟩` from `h`. Take `⟨l1, l2, l3⟩` from `La_round hK B`. Take `⟨-, -, g3, g4⟩` from `logs_of B`. Establish `hCH1 : 0 < K.CH` using `hK.2.1`. Establish `hCH4 : 4 * K.CH + 1 ≤ CH` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCH`.

Establish `h108 : (108 : ℝ) ≤ CH` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hCH`. Establish `hYb0 : 0 ≤ X.Yb` using `by linarith`. Establish `hN0 : (0 : ℝ) ≤ (X.TT.card : ℝ)` using `by positivity`. Establish `hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1` using `B.hk5`. Establish `hk0 : (0 : ℝ) < (X.m : ℝ) + 1` using `by linarith`.

Establish `hLa1 : 1 ≤ LaI K.C₀ X.N₁ X.ar` using `B.hLa1`. Establish `hLa'0 : 0 ≤ LaI K.C₀ X.N₁ X.a` using `by linarith`. Establish `hN1r : (1 : ℝ) ≤ (X.N₁ : ℝ)` using `B.hN1`. Establish `hY0 : 0 ≤ X.Y` using `by linarith`. Establish `hdd : deI K.CH K.C₀ X.m X.N₁ X.a X.b' X.bl X.bu + 1 / ((X.m : ℝ) + 1) ≤ deI CH K.C₀ X.m X.N₁ X.ar X.b' X.bl X.bu`.

Unfold `deI`. Conclude with `rde CH K.CH X.N₁ _ _ _ _ hCH1.le (by linarith) hN1r hLa1 l2 hk0`. Establish `hk1 : 0 < 1 / ((X.m : ℝ) + 1)` using `by positivity`. Establish `hde0 : 0 ≤ deI K.CH K.C₀ X.m X.N₁ X.a X.b' X.bl X.bu`. Unfold `deI`.

Establish `: 0 ≤ X.bu - X.bl` using `by linarith`. Check the signs of the components of the expression. Establish `hde6 : deI K.CH K.C₀ X.m X.N₁ X.a X.b' X.bl X.bu < 1 / 6` using `by linarith`. Establish `hka : (X.m : ℝ) + 1 ≤ X.ar`. Establish `h1 : (X.m : ℝ) + 1 ≤ X.p` using `B.hkp`.

Establish `h2` using `le_mul_of_one_le_right (by linarith [B.hp25] : (0 : ℝ) ≤ X.p) (by linarith [B.hb8] : (1 : ℝ) ≤ X.b')`. Combine the linear relations using `[B.hpa]`. Use `⟨hY, hp, hev, hseg2, hgap, hN1, hm, by linarith, hb, hbl, hbu, ?_, hIb2, by linarith, ?_, ?_, hde6, ?_, ?_, ?_, ?_, ?_, hcs, ?_⟩` and prove the remaining obligations. Conclude with `r12 _ _ _ _ _ _ _ hYb0 hN0 hb.le hk0 l2 hIb1`. Conclude with `r15 _ _ _ _ _ hYb0 hN0 l2 hk2`.

Conclude with `r16 _ _ _ _ _ _ _ _ _ _ _ hk0.le hY0 hYb0 hN0 hb B.haa l3 hab`. Conclude with `lt_of_lt_of_le hpab (div_le_div_of_nonneg_right B.haa hb.le)`. Conclude with `r19 CH _ _ _ _ _ hCH1.le (by linarith) hN0 hLa'0 l2 hkLa`. Introduce `d hd hc`. Conclude with `hband d hd (rband _ _ _ _ _ _ _ hb hk0 hka B.haa B.haa1.le hde0 hde6 hdd hc)`.

Establish `: LaI K.C₀ X.N₁ X.ar * X.b' / ((X.m : ℝ) + 1) ≤ LaI K.C₀ X.N₁ X.a * X.b' / ((X.m : ℝ) + 1)` using `div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right l1 hb.le) hk0.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hG : (0 : ℝ) ≤ (X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3)` using `by positivity`. Use `r22 CH K.CH _ _ _ _ hCH1.le (by linarith) hG (by linarith [B.hL1]) g4 (by calc CH * ((X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3)) * Real.logb X.p X.ar = CH * (X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3) * Real.logb X.p X.ar := by ring …` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.

Establish `hG : (0 : ℝ) ≤ ((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 * ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y` using `by positivity`. Use `mul_le_mul_of_nonneg_right (by linarith : K.CH ≤ CH) hG` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hyp_round {K : Cst} (hK : K.Pos) {CH : ℝ} (hCH : K.TM ≤ CH) {X : Dat} (h : X.Hyp K.C₀ CH) (B : Base K CH X) :
    HypI K.C₀ K.CH X.p X.n' X.m X.TT X.G' X.N₁ X.Y (X.Yb / 2) (X.a : ℝ) X.b' X.bl X.bu X.ccl X.Dp X.cStar := by
  obtain ⟨hY, hp, hev, hseg2, hgap, hN1, hm, hLa8, hb, hbl, hbu, hIb1, hIb2, hYb, hk2, hab, hde, hpab, hkLa, hband,
    hccl, hD, hcs, hsize⟩ := h
  obtain ⟨l1, l2, l3⟩ := La_round hK B
  obtain ⟨-, -, g3, g4⟩ := logs_of B
  have hCH1 : 0 < K.CH := hK.2.1
  have hCH4 : 4 * K.CH + 1 ≤ CH := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCH
  have h108 : (108 : ℝ) ≤ CH :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hCH
  have hYb0 : 0 ≤ X.Yb := by linarith
  have hN0 : (0 : ℝ) ≤ (X.TT.card : ℝ) := by positivity
  have hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1 := B.hk5
  have hk0 : (0 : ℝ) < (X.m : ℝ) + 1 := by linarith
  have hLa1 : 1 ≤ LaI K.C₀ X.N₁ X.ar := B.hLa1
  have hLa'0 : 0 ≤ LaI K.C₀ X.N₁ X.a := by linarith
  have hN1r : (1 : ℝ) ≤ (X.N₁ : ℝ) := B.hN1
  have hY0 : 0 ≤ X.Y := by linarith
  have hdd : deI K.CH K.C₀ X.m X.N₁ X.a X.b' X.bl X.bu + 1 / ((X.m : ℝ) + 1) ≤
      deI CH K.C₀ X.m X.N₁ X.ar X.b' X.bl X.bu := by
    unfold deI
    exact rde CH K.CH X.N₁ _ _ _ _ hCH1.le (by linarith) hN1r hLa1 l2 hk0
  have hk1 : 0 < 1 / ((X.m : ℝ) + 1) := by positivity
  have hde0 : 0 ≤ deI K.CH K.C₀ X.m X.N₁ X.a X.b' X.bl X.bu := by
    unfold deI
    have : 0 ≤ X.bu - X.bl := by linarith
    positivity
  have hde6 : deI K.CH K.C₀ X.m X.N₁ X.a X.b' X.bl X.bu < 1 / 6 := by linarith
  have hka : (X.m : ℝ) + 1 ≤ X.ar := by
    have h1 : (X.m : ℝ) + 1 ≤ X.p := B.hkp
    have h2 := le_mul_of_one_le_right (by linarith [B.hp25] : (0 : ℝ) ≤ X.p) (by linarith [B.hb8] : (1 : ℝ) ≤ X.b')
    linarith [B.hpa]
  refine ⟨hY, hp, hev, hseg2, hgap, hN1, hm, by linarith, hb, hbl, hbu, ?_, hIb2, by linarith, ?_, ?_, hde6, ?_, ?_,
    ?_, ?_, ?_, hcs, ?_⟩
  · exact r12 _ _ _ _ _ _ _ hYb0 hN0 hb.le hk0 l2 hIb1
  · exact r15 _ _ _ _ _ hYb0 hN0 l2 hk2
  · exact r16 _ _ _ _ _ _ _ _ _ _ _ hk0.le hY0 hYb0 hN0 hb B.haa l3 hab
  · exact lt_of_lt_of_le hpab (div_le_div_of_nonneg_right B.haa hb.le)
  · exact r19 CH _ _ _ _ _ hCH1.le (by linarith) hN0 hLa'0 l2 hkLa
  · intro d hd hc
    exact hband d hd (rband _ _ _ _ _ _ _ hb hk0 hka B.haa B.haa1.le hde0 hde6 hdd hc)
  · have : LaI K.C₀ X.N₁ X.ar * X.b' / ((X.m : ℝ) + 1) ≤ LaI K.C₀ X.N₁ X.a * X.b' / ((X.m : ℝ) + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right l1 hb.le) hk0.le
    linarith
  · have hG : (0 : ℝ) ≤ (X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3) := by positivity
    have := r22 CH K.CH _ _ _ _ hCH1.le (by linarith) hG (by linarith [B.hL1]) g4
      (by calc CH * ((X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3)) * Real.logb X.p X.ar
            = CH * (X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3) * Real.logb X.p X.ar := by ring
          _ ≤ (X.Dp : ℝ) := hD)
    calc K.CH * (X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3) * Real.logb X.p X.a
        = K.CH * ((X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3)) * Real.logb X.p X.a := by ring
      _ ≤ (X.Dp : ℝ) := this
  · have hG : (0 : ℝ) ≤ ((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
        ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y := by positivity
    have := mul_le_mul_of_nonneg_right (by linarith : K.CH ≤ CH) hG
    calc K.CH * ((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y
        = K.CH * (((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y) := by ring
      _ ≤ CH * (((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y) := this
      _ = CH * ((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y := by ring
      _ ≤ X.b' := hsize

end Formalism.MainNotions.flipOneThree.Pf

end
