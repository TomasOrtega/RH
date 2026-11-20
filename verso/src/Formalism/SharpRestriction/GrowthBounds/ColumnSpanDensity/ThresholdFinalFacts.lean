import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.NumBase
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ColumnSpanNumericalFacts

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

structure WinFacts (K : Cst) (X : Dat) : Prop where
  arnn : 0 ≤ X.ar
  uann : 0 ≤ X.ar + X.ar / (X.k * X.Y)
  blge : X.b' / 2 ≤ X.bl
  bule : X.bu ≤ 3 * X.b' / 2
  bunn : 0 ≤ X.bu
  wa_ge : X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' - 1 ≤ ((X.Wa 0).card : ℝ)
  wb_ge : X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' / X.k - 1 ≤ ((X.Wb 0).card : ℝ)

/- English proof (translation)
Simplify using `only [Dat.Wa, Nat.add_zero, Nat.card_Icc]`.
-/
theorem card_first_window (X : Dat) : (X.Wa 0).card = X.ua + 1 - X.a := by
  simp only [Dat.Wa, Nat.add_zero, Nat.card_Icc]

/- English proof (translation)
Simplify using `only [Dat.Wb, Nat.add_zero, Nat.card_Icc]`.
-/
theorem card_second_window (X : Dat) : (X.Wb 0).card = X.ub + 1 - X.lb := by
  simp only [Dat.Wb, Nat.add_zero, Nat.card_Icc]

/- English proof (translation)
Break down `le_total y x with hxy | hxy` into its components or cases. Rewrite using `[Nat.cast_sub hxy]`. Rewrite using `[Nat.sub_eq_zero_of_le hxy, Nat.cast_zero, sub_nonpos]`. Conclude with `hxy` after adjusting the coercions.
-/
private theorem natCast_sub_le_natCast_natSub (x y : ℕ) : (x : ℝ) - y ≤ ((x - y : ℕ) : ℝ) := by
  rcases le_total y x with hxy | hxy
  · rw [Nat.cast_sub hxy]
  · rw [Nat.sub_eq_zero_of_le hxy, Nat.cast_zero, sub_nonpos]
    exact_mod_cast hxy

/- English proof (translation)
Establish `B` using `base_of K hK CH hCH X h`. Establish `hH` using `h`. Unfold `Dat.Hyp HypI at hH`. Take `⟨_, _, _, _, _, _, _, _, h9, h10, h11, h12, h13, h14, _, h16, _, _, _, _, _, _, h23, h24⟩` from `hH`. Establish `hN : (X.TT.card : ℝ) = X.N` using `rfl`.

Establish `hk : (X.m : ℝ) + 1 = X.k` using `rfl`. Rewrite `h12`, `h16` using `[hN, hk]`. Establish `har : 0 < X.ar`. Establish `: 0 ≤ (X.p : ℝ) * X.b'` using `by positivity`. Combine the linear relations using `[B.hpa]`.

Establish `hk0 : 0 < X.k` using `by linarith [B.hk5]`. Establish `hY` using `B.hY`. Establish `hY0 : 0 < X.Y` using `by linarith`. Establish `h108 : (108 : ℝ) ≤ CH` using `le_trans ((le_max_left _ _).trans (le_max_left _ _)) hCH`. Establish `hYb : 0 ≤ X.Yb` using `by linarith`.

Establish `hLa` using `B.hLa1`. Establish `hN0 : (0 : ℝ) ≤ X.N` using `by positivity`. Use `⟨har.le, by positivity, by linarith, by linarith, by linarith, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[card_first_window]`. Establish `e1` using `Nat.lt_floor_add_one (X.ar + X.ar / (X.k * X.Y))`.

Establish `e2` using `B.haa1`. Establish `e3` using `natCast_sub_le_natCast_natSub (X.ua + 1) X.a`. Move the coercions through the operations in `at e3`. Establish `hkey : X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' ≤ X.ar / (X.k * X.Y)`. Rewrite using `[le_div_iff₀ (by positivity)]`.

Establish `f1 : X.k * X.Y ^ 2 * X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * Real.log X.ar * X.b' ≤ X.ar`. Rewrite `h16` using `[le_div_iff₀ h9]`. Then use the resulting hypothesis. Establish `hYl : 1 ≤ X.Y * Real.log X.ar` using `one_le_mul_of_one_le_of_one_le hY B.hlog1`. Establish `hpos : 0 ≤ X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' * (X.k * X.Y)` using `by positivity`. Establish `f2` using `mul_le_mul_of_nonneg_left hYl hpos`.

Use the polynomial consequences of the given equalities and inequalities. Establish `e4 : (X.ua : ℝ) = ⌊X.ar + X.ar / (X.k * X.Y)⌋₊` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[card_second_window]`. Establish `e1` using `Nat.lt_floor_add_one X.bu`.

Establish `e2` using `Nat.ceil_lt_add_one (show 0 ≤ X.bl by linarith)`. Establish `e3` using `natCast_sub_le_natCast_natSub (X.ub + 1) X.lb`. Move the coercions through the operations in `at e3`. Establish `e4 : (X.ub : ℝ) = ⌊X.bu⌋₊` using `rfl`. Establish `e5 : (X.lb : ℝ) = ⌈X.bl⌉₊` using `rfl`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem winFacts_of (K : Cst) (hK : K.Pos) (CH : ℝ) (hCH : K.TLP ≤ CH) (X : Dat) (h : X.Hyp K.C₀ CH) :
    WinFacts K X := by
  have B := base_of K hK CH hCH X h
  have hH := h
  unfold Dat.Hyp HypI at hH
  obtain ⟨_, _, _, _, _, _, _, _, h9, h10, h11, h12, h13, h14, _, h16, _, _, _, _, _, _, h23, h24⟩ := hH
  have hN : (X.TT.card : ℝ) = X.N := rfl
  have hk : (X.m : ℝ) + 1 = X.k := rfl
  rw [hN, hk] at h12 h16
  have har : 0 < X.ar := by
    have : 0 ≤ (X.p : ℝ) * X.b' := by positivity
    linarith [B.hpa]
  have hk0 : 0 < X.k := by linarith [B.hk5]
  have hY := B.hY
  have hY0 : 0 < X.Y := by linarith
  have h108 : (108 : ℝ) ≤ CH := le_trans ((le_max_left _ _).trans (le_max_left _ _)) hCH
  have hYb : 0 ≤ X.Yb := by linarith
  have hLa := B.hLa1
  have hN0 : (0 : ℝ) ≤ X.N := by positivity
  refine ⟨har.le, by positivity, by linarith, by linarith, by linarith, ?_, ?_⟩
  · rw [card_first_window]
    have e1 := Nat.lt_floor_add_one (X.ar + X.ar / (X.k * X.Y))
    have e2 := B.haa1
    have e3 := natCast_sub_le_natCast_natSub (X.ua + 1) X.a
    push_cast at e3
    have hkey : X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' ≤ X.ar / (X.k * X.Y) := by
      rw [le_div_iff₀ (by positivity)]
      have f1 : X.k * X.Y ^ 2 * X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * Real.log X.ar * X.b' ≤ X.ar := by
        rwa [le_div_iff₀ h9] at h16
      have hYl : 1 ≤ X.Y * Real.log X.ar := one_le_mul_of_one_le_of_one_le hY B.hlog1
      have hpos : 0 ≤ X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' * (X.k * X.Y) := by positivity
      have f2 := mul_le_mul_of_nonneg_left hYl hpos
      nlinarith
    have e4 : (X.ua : ℝ) = ⌊X.ar + X.ar / (X.k * X.Y)⌋₊ := rfl
    linarith
  · rw [card_second_window]
    have e1 := Nat.lt_floor_add_one X.bu
    have e2 := Nat.ceil_lt_add_one (show 0 ≤ X.bl by linarith)
    have e3 := natCast_sub_le_natCast_natSub (X.ub + 1) X.lb
    push_cast at e3
    have e4 : (X.ub : ℝ) = ⌊X.bu⌋₊ := rfl
    have e5 : (X.lb : ℝ) = ⌈X.bl⌉₊ := rfl
    linarith

/- English proof (translation)
Break down `Nat.eq_zero_or_pos N with hN | hN` into its components or cases. Substitute `hN` using the available equality. Simplify using `only [pow_zero, mul_one, sub_self]`. Check the signs of the components of the expression. Establish `hY0 : 0 < Y` using `by linarith`.

Establish `hA : (0 : ℝ) < wa` using `by exact_mod_cast hwa`. Establish `hB : (0 : ℝ) < wb` using `by exact_mod_cast hwb`. Establish `hN1 : (1 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `hc0 : (0 : ℝ) ≤ c` using `by positivity`. Establish `h2YN : 1 ≤ 2 * Y * N` using `by nlinarith`.

Establish `hcc` using `mul_le_mul_of_nonneg_right h2YN hc0`. Establish `hca : (c : ℝ) ≤ wa` using `by linarith`. Establish `hcb : (c : ℝ) ≤ wb` using `by linarith`. Establish `hca' : c ≤ wa` using `by exact_mod_cast hca`. Establish `hcb' : c ≤ wb` using `by exact_mod_cast hcb`.

Rewrite using `[Nat.cast_sub hca', Nat.cast_sub hcb']`. Establish `bern : ∀ A : ℝ, 0 < A → (c : ℝ) ≤ A → A ^ N * (1 - N * c / A) ≤ (A - c) ^ N`. Introduce `A hA hcA`. Establish `hq : -2 ≤ -((c : ℝ) / A)`. Establish `: (c : ℝ) / A ≤ 1` using `(div_le_one hA).2 hcA`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb` using `one_add_mul_le_pow hq N`. Establish `e : (A - c) ^ N = A ^ N * (1 + -((c : ℝ) / A)) ^ N`. Rewrite using `[← mul_pow]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Establish `e2 : 1 - (N : ℝ) * c / A = 1 + (N : ℝ) * -((c : ℝ) / A)` using `by ring`. Rewrite using `[e2]`.

Conclude with `mul_le_mul_of_nonneg_left hb (by positivity)`. Establish `hpa : (N : ℝ) * c / wa ≤ 1 / (2 * Y)`. Rewrite using `[div_le_div_iff₀ hA (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hpb : (N : ℝ) * c / wb ≤ 1 / (2 * Y)`.

Rewrite using `[div_le_div_iff₀ hB (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hp0 : 0 ≤ (N : ℝ) * c / wa` using `by positivity`. Establish `hq0 : 0 ≤ (N : ℝ) * c / wb` using `by positivity`. Establish `hhalf : 1 / (2 * Y) ≤ 1 / 2`.

Rewrite using `[div_le_div_iff₀ (by positivity) (by norm_num)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `bern wa hA hca`. Establish `h2` using `bern wb hB hcb`. Use `set p := (N : ℝ) * c / wa`.

Use `set q := (N : ℝ) * c / wb`. Establish `hX : 0 ≤ (wa : ℝ) ^ N * (wb : ℝ) ^ N` using `by positivity`. Establish `hprod : (wa : ℝ) ^ N * (1 - p) * ((wb : ℝ) ^ N * (1 - q)) ≤ ((wa : ℝ) - c) ^ N * ((wb : ℝ) - c) ^ N` using `mul_le_mul h1 h2 (by nlinarith [pow_pos hB N]) (by nlinarith [pow_pos hA N])`. Establish `hpq : 1 - 1 / Y ≤ (1 - p) * (1 - q)`. Establish `e : 1 / Y = 1 / (2 * Y) + 1 / (2 * Y)` using `by field_simp; ring`.

Use polynomial arithmetic with `[mul_nonneg hp0 hq0]`. Establish `h3 : (wa : ℝ) ^ N * (wb : ℝ) ^ N * (1 - 1 / Y) ≤ (wa : ℝ) ^ N * (wb : ℝ) ^ N * ((1 - p) * (1 - q))` using `mul_le_mul_of_nonneg_left hpq hX`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem below_abs (N wa wb c : ℕ) (Y : ℝ) (hY : 1 ≤ Y) (ha : 2 * Y * N * c ≤ wa) (hb : 2 * Y * N * c ≤ wb)
    (hwa : 0 < wa) (hwb : 0 < wb) :
    (wa : ℝ) ^ N * (wb : ℝ) ^ N - ((wa - c : ℕ) : ℝ) ^ N * ((wb - c : ℕ) : ℝ) ^ N ≤
      1 / Y * ((wa : ℝ) ^ N * (wb : ℝ) ^ N) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [pow_zero, mul_one, sub_self]
    positivity
  have hY0 : 0 < Y := by linarith
  have hA : (0 : ℝ) < wa := by exact_mod_cast hwa
  have hB : (0 : ℝ) < wb := by exact_mod_cast hwb
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have h2YN : 1 ≤ 2 * Y * N := by nlinarith
  have hcc := mul_le_mul_of_nonneg_right h2YN hc0
  have hca : (c : ℝ) ≤ wa := by linarith
  have hcb : (c : ℝ) ≤ wb := by linarith
  have hca' : c ≤ wa := by exact_mod_cast hca
  have hcb' : c ≤ wb := by exact_mod_cast hcb
  rw [Nat.cast_sub hca', Nat.cast_sub hcb']

  have bern : ∀ A : ℝ, 0 < A → (c : ℝ) ≤ A → A ^ N * (1 - N * c / A) ≤ (A - c) ^ N := by
    intro A hA hcA
    have hq : -2 ≤ -((c : ℝ) / A) := by
      have : (c : ℝ) / A ≤ 1 := (div_le_one hA).2 hcA
      linarith
    have hb := one_add_mul_le_pow hq N
    have e : (A - c) ^ N = A ^ N * (1 + -((c : ℝ) / A)) ^ N := by
      rw [← mul_pow]
      congr 1
      field_simp
      ring
    rw [e]
    have e2 : 1 - (N : ℝ) * c / A = 1 + (N : ℝ) * -((c : ℝ) / A) := by ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hpa : (N : ℝ) * c / wa ≤ 1 / (2 * Y) := by
    rw [div_le_div_iff₀ hA (by positivity)]
    nlinarith
  have hpb : (N : ℝ) * c / wb ≤ 1 / (2 * Y) := by
    rw [div_le_div_iff₀ hB (by positivity)]
    nlinarith
  have hp0 : 0 ≤ (N : ℝ) * c / wa := by positivity
  have hq0 : 0 ≤ (N : ℝ) * c / wb := by positivity
  have hhalf : 1 / (2 * Y) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h1 := bern wa hA hca
  have h2 := bern wb hB hcb
  set p := (N : ℝ) * c / wa
  set q := (N : ℝ) * c / wb
  have hX : 0 ≤ (wa : ℝ) ^ N * (wb : ℝ) ^ N := by positivity
  have hprod : (wa : ℝ) ^ N * (1 - p) * ((wb : ℝ) ^ N * (1 - q)) ≤ ((wa : ℝ) - c) ^ N * ((wb : ℝ) - c) ^ N :=
    mul_le_mul h1 h2 (by nlinarith [pow_pos hB N]) (by nlinarith [pow_pos hA N])
  have hpq : 1 - 1 / Y ≤ (1 - p) * (1 - q) := by
    have e : 1 / Y = 1 / (2 * Y) + 1 / (2 * Y) := by field_simp; ring
    nlinarith [mul_nonneg hp0 hq0]
  have h3 : (wa : ℝ) ^ N * (wb : ℝ) ^ N * (1 - 1 / Y) ≤ (wa : ℝ) ^ N * (wb : ℝ) ^ N * ((1 - p) * (1 - q)) :=
    mul_le_mul_of_nonneg_left hpq hX
  nlinarith

/- English proof (translation)
Establish `h108T : (108 : ℝ) ≤ K.TLP` using `(le_max_left _ _).trans (le_max_left _ _)`. Use `⟨K.TLP, 1, by linarith, one_pos, ?_⟩` and prove the remaining obligations. Introduce `CH hCH C _ X h`. Establish `W` using `winFacts_of K hK CH hCH X h`. Establish `B` using `base_of K hK CH hCH X h`.

Establish `hH` using `h`. Unfold `Dat.Hyp HypI at hH`. Take `⟨_, _, _, _, _, _, _, _, h9, h10, h11, h12, h13, h14, _, h16, _, _, _, _, _, _, h23, h24⟩` from `hH`. Establish `hN : (X.TT.card : ℝ) = X.N` using `rfl`. Establish `hk : (X.m : ℝ) + 1 = X.k` using `rfl`.

Rewrite `h24` using `[hN, hk]`. Establish `h108 : (108 : ℝ) ≤ CH` using `le_trans h108T hCH`. Establish `hY` using `B.hY`. Establish `hk5` using `B.hk5`. Establish `hN2` using `B.hN2`.

Establish `hLa` using `B.hLa1`. Establish `hk0 : 0 < X.k` using `by linarith`. Establish `hYb : (108 : ℝ) ≤ X.Yb` using `by linarith`. Establish `hq : (1 : ℝ) ≤ ((X.p : ℝ) ^ X.G') ^ 4` using `one_le_pow₀ B.hQ`. Establish `hc8 : (8 : ℝ) ≤ X.cStar`.

Establish `: 8 ≤ X.cStar` using `le_trans (by omega) h23`. Conclude with `this` after adjusting the coercions. Establish `hS : (8 : ℝ) ≤ (X.cStar : ℝ) + X.N * X.ccl + X.n' * X.ccl`. Establish `: (0 : ℝ) ≤ X.N * X.ccl + X.n' * X.ccl` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hSN : (X.N : ℝ) * X.ccl ≤ (X.cStar : ℝ) + X.N * X.ccl + X.n' * X.ccl`. Establish `: (0 : ℝ) ≤ X.cStar + X.n' * X.ccl` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set S := (X.cStar : ℝ) + X.N * X.ccl + X.n' * X.ccl with hSdef`. Use `set q := ((X.p : ℝ) ^ X.G') ^ 4 with hqdef`.

Establish `hN1 : (1 : ℝ) ≤ X.N` using `by linarith`. Establish `hcc : (X.ccl : ℝ) ≤ q * S`. Establish `hc0 : (0 : ℝ) ≤ X.ccl` using `by positivity`. Establish `e1 : (X.ccl : ℝ) ≤ X.N * X.ccl` using `le_mul_of_one_le_left hc0 hN1`. Establish `e2 : S ≤ q * S` using `le_mul_of_one_le_left (by linarith) hq`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hR : 0 ≤ CH * X.k ^ 3 * X.N * X.Y`. Establish `: 0 ≤ CH` using `by linarith`. Check the signs of the components of the expression. Establish `hC : CH * X.k ^ 3 * (X.N * X.ccl * X.Y) ≤ X.b'`.

Combine the equalities or inequalities in the displayed calculation. Establish `hk2 : (25 : ℝ) ≤ X.k ^ 2`. Use `pow_le_pow_left₀ (by norm_num) hk5 2` as an intermediate fact. Evaluate the numerical expressions using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hCk2 : (2700 : ℝ) ≤ CH * X.k ^ 2`. Use `mul_le_mul h108 hk2 (by norm_num) (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbk : X.k ≤ X.b'`. Establish `f1 : (1 : ℝ) ≤ CH * X.k ^ 2` using `by linarith`.

Establish `f2 : (1 : ℝ) ≤ CH * X.k ^ 2 * X.N` using `one_le_mul_of_one_le_of_one_le f1 hN1`. Establish `f3 : (1 : ℝ) ≤ CH * X.k ^ 2 * X.N * q` using `one_le_mul_of_one_le_of_one_le f2 hq`. Establish `f4 : (1 : ℝ) ≤ CH * X.k ^ 2 * X.N * q * S` using `one_le_mul_of_one_le_of_one_le f3 (by linarith)`. Establish `f5 : (1 : ℝ) ≤ CH * X.k ^ 2 * X.N * q * S * X.Y` using `one_le_mul_of_one_le_of_one_le f4 hY`. Establish `f6` using `mul_le_mul_of_nonneg_left f5 hk0.le`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hu : (0 : ℝ) ≤ X.N * X.ccl * X.Y` using `by positivity`. Establish `h2k : 2 * X.k ≤ CH * X.k ^ 3`. Use `mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ CH * X.k ^ 2 by linarith) hk0.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h2uk` using `mul_le_mul_of_nonneg_right h2k hu`. Establish `hQ1 : (108 : ℝ) * 2 ≤ X.Yb * X.N` using `mul_le_mul hYb hN2 (by norm_num) (by linarith)`. Establish `hQ2 : (216 : ℝ) ≤ X.Yb * X.N * LaI K.C₀ X.N₁ X.ar`. Use `mul_le_mul hQ1 hLa (by norm_num) (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hb8` using `B.hb8`. Establish `hQb : (216 : ℝ) * X.b' ≤ X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b'` using `mul_le_mul_of_nonneg_right hQ2 (by linarith)`. Establish `h2u : 2 * (X.N * X.ccl * X.Y) ≤ CH * X.k ^ 3 * (X.N * X.ccl * X.Y)` using `mul_le_mul_of_nonneg_right (by linarith) hu`. Establish `hwa` using `W.wa_ge`. Establish `hwb` using `W.wb_ge`.

Establish `hwbD : X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' / X.k - 1 ≥ 2 * X.Y * X.N * X.ccl`. Rewrite using `[ge_iff_le, le_sub_iff_add_le, le_div_iff₀ hk0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `haN : 2 * X.Y * X.N * X.ccl ≤ ((X.Wa 0).card : ℝ)` using `by linarith`. Establish `hbN : 2 * X.Y * X.N * X.ccl ≤ ((X.Wb 0).card : ℝ)` using `by linarith`.

Establish `hwa0 : 0 < (X.Wa 0).card`. Establish `: (0 : ℝ) < (X.Wa 0).card` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `hwb0 : 0 < (X.Wb 0).card`. Establish `: (0 : ℝ) < (X.Wb 0).card`.

Establish `: (1 : ℝ) ≤ X.b' / X.k` using `(one_le_div hk0).2 hbk`. Establish `e : X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' / X.k = X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * (X.b' / X.k)`. Expand and normalize the polynomial expressions, which then agree. Use `mul_le_mul hQ2 this (by norm_num) (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `this` after adjusting the coercions. Establish `ea : (Finset.Icc (X.a + X.ccl) X.ua).card = (X.Wa 0).card - X.ccl`. Rewrite using `[Nat.card_Icc, card_first_window, Nat.sub_sub]`. Establish `eb : (Finset.Icc (X.lb + X.ccl) X.ub).card = (X.Wb 0).card - X.ccl`. Rewrite using `[Nat.card_Icc, card_second_window, Nat.sub_sub]`.

Use `⟨W.arnn, W.uann, by linarith [W.blge], W.bunn, hY, by exact_mod_cast B.hN1, by exact_mod_cast (show (1 : ℝ) ≤ X.N by linarith), ⟨hwa0, hwb0⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ea, eb]`. Conclude with `below_abs X.N _ _ X.ccl X.Y hY haN hbN hwa0 hwb0`. Establish `hb0 : 0 < X.b'` using `by linarith`. Establish `hY0 : 0 < X.Y` using `by linarith`.

Rewrite using `[div_le_div_iff₀ hb0 hY0]`. Establish `h12k : 12 * X.k ≤ CH * X.k ^ 3`. Use `mul_le_mul_of_nonneg_right (show (12 : ℝ) ≤ CH * X.k ^ 2 by linarith) hk0.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `mul_le_mul_of_nonneg_right h12k hu` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem threshold_final_facts (K : Cst) (hK : K.Pos) : TransportedAlt K (fun _ => ColumnSpanNumericalFacts K) := by
  have h108T : (108 : ℝ) ≤ K.TLP := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨K.TLP, 1, by linarith, one_pos, ?_⟩
  intro CH hCH C _ X h
  have W := winFacts_of K hK CH hCH X h
  have B := base_of K hK CH hCH X h
  have hH := h
  unfold Dat.Hyp HypI at hH
  obtain ⟨_, _, _, _, _, _, _, _, h9, h10, h11, h12, h13, h14, _, h16, _, _, _, _, _, _, h23, h24⟩ := hH
  have hN : (X.TT.card : ℝ) = X.N := rfl
  have hk : (X.m : ℝ) + 1 = X.k := rfl
  rw [hN, hk] at h24
  have h108 : (108 : ℝ) ≤ CH := le_trans h108T hCH
  have hY := B.hY
  have hk5 := B.hk5
  have hN2 := B.hN2
  have hLa := B.hLa1
  have hk0 : 0 < X.k := by linarith
  have hYb : (108 : ℝ) ≤ X.Yb := by linarith
  have hq : (1 : ℝ) ≤ ((X.p : ℝ) ^ X.G') ^ 4 := one_le_pow₀ B.hQ
  have hc8 : (8 : ℝ) ≤ X.cStar := by
    have : 8 ≤ X.cStar := le_trans (by omega) h23
    exact_mod_cast this
  have hS : (8 : ℝ) ≤ (X.cStar : ℝ) + X.N * X.ccl + X.n' * X.ccl := by
    have : (0 : ℝ) ≤ X.N * X.ccl + X.n' * X.ccl := by positivity
    linarith
  have hSN : (X.N : ℝ) * X.ccl ≤ (X.cStar : ℝ) + X.N * X.ccl + X.n' * X.ccl := by
    have : (0 : ℝ) ≤ X.cStar + X.n' * X.ccl := by positivity
    linarith
  set S := (X.cStar : ℝ) + X.N * X.ccl + X.n' * X.ccl with hSdef
  set q := ((X.p : ℝ) ^ X.G') ^ 4 with hqdef
  have hN1 : (1 : ℝ) ≤ X.N := by linarith
  have hcc : (X.ccl : ℝ) ≤ q * S := by
    have hc0 : (0 : ℝ) ≤ X.ccl := by positivity
    have e1 : (X.ccl : ℝ) ≤ X.N * X.ccl := le_mul_of_one_le_left hc0 hN1
    have e2 : S ≤ q * S := le_mul_of_one_le_left (by linarith) hq
    linarith
  have hR : 0 ≤ CH * X.k ^ 3 * X.N * X.Y := by
    have : 0 ≤ CH := by linarith
    positivity
  have hC : CH * X.k ^ 3 * (X.N * X.ccl * X.Y) ≤ X.b' := by
    calc CH * X.k ^ 3 * (X.N * X.ccl * X.Y) = CH * X.k ^ 3 * X.N * X.Y * X.ccl := by ring
      _ ≤ CH * X.k ^ 3 * X.N * X.Y * (q * S) := mul_le_mul_of_nonneg_left hcc hR
      _ = CH * X.k ^ 3 * X.N * q * S * X.Y := by ring
      _ ≤ X.b' := h24
  have hk2 : (25 : ℝ) ≤ X.k ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) hk5 2
    norm_num at this
    linarith
  have hCk2 : (2700 : ℝ) ≤ CH * X.k ^ 2 := by
    have := mul_le_mul h108 hk2 (by norm_num) (by linarith)
    linarith
  have hbk : X.k ≤ X.b' := by
    have f1 : (1 : ℝ) ≤ CH * X.k ^ 2 := by linarith
    have f2 : (1 : ℝ) ≤ CH * X.k ^ 2 * X.N := one_le_mul_of_one_le_of_one_le f1 hN1
    have f3 : (1 : ℝ) ≤ CH * X.k ^ 2 * X.N * q := one_le_mul_of_one_le_of_one_le f2 hq
    have f4 : (1 : ℝ) ≤ CH * X.k ^ 2 * X.N * q * S := one_le_mul_of_one_le_of_one_le f3 (by linarith)
    have f5 : (1 : ℝ) ≤ CH * X.k ^ 2 * X.N * q * S * X.Y := one_le_mul_of_one_le_of_one_le f4 hY
    have f6 := mul_le_mul_of_nonneg_left f5 hk0.le
    linarith
  have hu : (0 : ℝ) ≤ X.N * X.ccl * X.Y := by positivity
  have h2k : 2 * X.k ≤ CH * X.k ^ 3 := by
    have := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ CH * X.k ^ 2 by linarith) hk0.le
    linarith
  have h2uk := mul_le_mul_of_nonneg_right h2k hu
  have hQ1 : (108 : ℝ) * 2 ≤ X.Yb * X.N := mul_le_mul hYb hN2 (by norm_num) (by linarith)
  have hQ2 : (216 : ℝ) ≤ X.Yb * X.N * LaI K.C₀ X.N₁ X.ar := by
    have := mul_le_mul hQ1 hLa (by norm_num) (by linarith)
    linarith
  have hb8 := B.hb8
  have hQb : (216 : ℝ) * X.b' ≤ X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' :=
    mul_le_mul_of_nonneg_right hQ2 (by linarith)
  have h2u : 2 * (X.N * X.ccl * X.Y) ≤ CH * X.k ^ 3 * (X.N * X.ccl * X.Y) :=
    mul_le_mul_of_nonneg_right (by linarith) hu
  have hwa := W.wa_ge
  have hwb := W.wb_ge
  have hwbD : X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' / X.k - 1 ≥ 2 * X.Y * X.N * X.ccl := by
    rw [ge_iff_le, le_sub_iff_add_le, le_div_iff₀ hk0]
    linarith
  have haN : 2 * X.Y * X.N * X.ccl ≤ ((X.Wa 0).card : ℝ) := by linarith
  have hbN : 2 * X.Y * X.N * X.ccl ≤ ((X.Wb 0).card : ℝ) := by linarith
  have hwa0 : 0 < (X.Wa 0).card := by
    have : (0 : ℝ) < (X.Wa 0).card := by linarith
    exact_mod_cast this
  have hwb0 : 0 < (X.Wb 0).card := by
    have : (0 : ℝ) < (X.Wb 0).card := by
      have : (1 : ℝ) ≤ X.b' / X.k := (one_le_div hk0).2 hbk
      have e : X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' / X.k = X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * (X.b' / X.k) := by
        ring
      have := mul_le_mul hQ2 this (by norm_num) (by linarith)
      linarith
    exact_mod_cast this
  have ea : (Finset.Icc (X.a + X.ccl) X.ua).card = (X.Wa 0).card - X.ccl := by
    rw [Nat.card_Icc, card_first_window, Nat.sub_sub]
  have eb : (Finset.Icc (X.lb + X.ccl) X.ub).card = (X.Wb 0).card - X.ccl := by
    rw [Nat.card_Icc, card_second_window, Nat.sub_sub]
  refine ⟨W.arnn, W.uann, by linarith [W.blge], W.bunn, hY, by exact_mod_cast B.hN1,
    by exact_mod_cast (show (1 : ℝ) ≤ X.N by linarith), ⟨hwa0, hwb0⟩, ?_, ?_⟩
  · rw [ea, eb]
    exact below_abs X.N _ _ X.ccl X.Y hY haN hbN hwa0 hwb0
  · have hb0 : 0 < X.b' := by linarith
    have hY0 : 0 < X.Y := by linarith
    rw [div_le_div_iff₀ hb0 hY0]
    have h12k : 12 * X.k ≤ CH * X.k ^ 3 := by
      have := mul_le_mul_of_nonneg_right (show (12 : ℝ) ≤ CH * X.k ^ 2 by linarith) hk0.le
      linarith
    have := mul_le_mul_of_nonneg_right h12k hu
    linarith

end Formalism.MainNotions.flipOneThree.Pf

end
