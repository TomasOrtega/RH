import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SymbolFormOfOrthogonality

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

/- English proof (translation)
Introduce `X hD hH hC j b hk`. Establish `St` using `hstd X hD hH hC`. Establish `hO` using `(segHyp_of St j).oplus b`. Establish `hk4` using `hk.2.2.2`. Establish `hSa : (((X.seg C0 CE1 CE2 j).a : ℕ) : ℝ) = (X.a : ℝ)` using `rfl`.

Establish `hSLa : (X.seg C0 CE1 CE2 j).La = X.La C0` using `rfl`. Rewrite `hO` using `[hSa, hSLa]`. Use `set A : ℝ := (X.a : ℝ) with hA`. Use `set P : ℝ := (X.p : ℝ) with hPdef`. Use `set La : ℝ := X.La C0 with hLadef`.

Use `set s : ℝ := (segS X.TT j : ℝ) with hsdef`. Use `set q : ℝ := (X.m : ℝ) + 1 with hq`. Establish `hP5 : (5 : ℝ) ≤ P` using `by show (5 : ℝ) ≤ (X.p : ℝ)`. Conclude with `St.p5` after adjusting the coercions. Establish `hP : (0 : ℝ) < P` using `by linarith`.

Establish `ha : (0 : ℝ) ≤ A` using `Nat.cast_nonneg _`. Establish `hb : 0 < X.b'` using `St.bpos`. Establish `hbp : X.b' * P < A`. Establish `h1 : P < A / X.b'` using `St.pab`. Rewrite `h1` using `[lt_div_iff₀ hb]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hY` using `St.Y1`. Establish `hk2 : X.k ^ 2 ≤ P`. Establish `h1 : X.k ^ 2 * X.Y ^ 2 ≤ P` using `St.pk`. Establish `hY2 : (1 : ℝ) ≤ X.Y ^ 2` using `one_le_pow₀ hY`.

Establish `h2 : X.k ^ 2 * 1 ≤ X.k ^ 2 * X.Y ^ 2` using `mul_le_mul_of_nonneg_left hY2 (sq_nonneg X.k)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN1 : (1 : ℝ) ≤ X.N1` using `by exact_mod_cast St.N1pos`. Establish `hk5 : 5 ≤ X.k` using `by linarith [St.N1k]`. Establish `hkP : 5 * X.k ≤ P` using `by nlinarith`.

Establish `hN2 : (2 : ℝ) ≤ X.N` using `by exact_mod_cast St.N2`. Establish `hLa1 : 1 ≤ La` using `St.La1`. Establish `hLaN : 2 * X.N * La ≤ X.k` using `St.LaN`. Establish `hLa : 4 * La ≤ X.k` using `by nlinarith`. Establish `hsN : s ≤ X.N1` using `by show ((segS X.TT j : ℕ) : ℝ) ≤ (X.N1 : ℝ)`.

Conclude with `(St.segB j).2` after adjusting the coercions. Establish `hs0 : 0 ≤ s` using `Nat.cast_nonneg _`. Establish `hs2 : 2 * s ≤ X.k` using `by linarith [St.N1k]`. Establish `hq1 : 1 ≤ q` using `by rw [hq]; linarith [(Nat.cast_nonneg X.m : (0 : ℝ) ≤ X.m)]`. Establish `e1 : A / P ^ 2 ≤ A / 25` using `div_le_div_of_nonneg_left ha (by norm_num) (by nlinarith)`.

Establish `e2 : s * (2 * (X.b' / P)) ≤ A / 25`. Rewrite using `[show s * (2 * (X.b' / P)) = 2 * s * X.b' / P by ring, div_le_div_iff₀ hP (by norm_num)]`. Establish `f1` using `mul_le_mul_of_nonneg_right hs2 hb.le`. Establish `f2` using `mul_le_mul_of_nonneg_right hkP hb.le`. Establish `f3` using `mul_le_mul_of_nonneg_right hP5 ha`.

Use the polynomial consequences of the given equalities and inequalities. Establish `e3 : (La / q + 4 / P ^ 2) * (s * (2 * A / P)) ≤ A / 4 + 4 * A / 125`. Establish `hsA : 0 ≤ s * (2 * A / P)` using `by positivity`. Establish `g1 : (La / q + 4 / P ^ 2) * (s * (2 * A / P)) ≤ (La + 4 / P ^ 2) * (s * (2 * A / P))` using `mul_le_mul_of_nonneg_right (by`. Use `div_le_self (show (0 : ℝ) ≤ La by linarith) hq1` as an intermediate fact.

Use the proof step `linarith) hsA`. Establish `g2 : (La + 4 / P ^ 2) * (s * (2 * A / P)) = 2 * La * s * A / P + 8 * s * A / P ^ 3`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `g3 : 2 * La * s * A / P ≤ A / 4`.

Rewrite using `[div_le_div_iff₀ hP (by norm_num)]`. Establish `hm` using `mul_le_mul hLa hs2 (by positivity) (by linarith)`. Establish `h8 : 8 * (La * s) ≤ P`. Establish `e : X.k * X.k = X.k ^ 2` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h9` using `mul_le_mul_of_nonneg_right h8 ha`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `g4 : 8 * s * A / P ^ 3 ≤ 4 * A / 125`. Rewrite using `[div_le_div_iff₀ (by positivity) (by norm_num)]`. Establish `h1 : 8 * s ≤ 4 * P / 5` using `by linarith`.

Establish `h2 : (25 : ℝ) ≤ P ^ 2`. Use `mul_le_mul hP5 hP5 (by norm_num) hP.le` as an intermediate fact. Rewrite using `[sq]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : 8 * s * A * 125 ≤ 100 * P * A`.

Use `mul_le_mul_of_nonneg_right h1 ha` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : 100 * P * A ≤ 4 * A * P ^ 3`. Establish `h5` using `mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * A * P)`. Establish `e : 4 * A * P * P ^ 2 = 4 * A * P ^ 3` using `by ring`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e4 : 2 * (La * X.b' / q) ≤ A / 10`. Establish `g1 : La * X.b' / q ≤ La * X.b'` using `div_le_self (by positivity) hq1`.

Establish `g2 : 20 * (La * X.b') ≤ A`. Establish `f1` using `mul_le_mul_of_nonneg_right hLa hb.le`. Establish `f2` using `mul_le_mul_of_nonneg_right hkP hb.le`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hwin` using `((St.winA _ (next_mem X.TT j).1).1)`. Establish `hfin : (b.oPlus : ℝ) ≤ (X.aT (segNext X.TT j) : ℝ)`. Use `hO` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `segAPlus`.

Conclude with `hfin` after adjusting the coercions.
-/
theorem oPlusAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X) :
    OPlusAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X hD hH hC j b hk
  have St := hstd X hD hH hC
  have hO := (segHyp_of St j).oplus b
  have hk4 := hk.2.2.2

  have hSa : (((X.seg C0 CE1 CE2 j).a : ℕ) : ℝ) = (X.a : ℝ) := rfl
  have hSLa : (X.seg C0 CE1 CE2 j).La = X.La C0 := rfl
  rw [hSa, hSLa] at hO
  set A : ℝ := (X.a : ℝ) with hA
  set P : ℝ := (X.p : ℝ) with hPdef
  set La : ℝ := X.La C0 with hLadef
  set s : ℝ := (segS X.TT j : ℝ) with hsdef
  set q : ℝ := (X.m : ℝ) + 1 with hq
  have hP5 : (5 : ℝ) ≤ P := by
    show (5 : ℝ) ≤ (X.p : ℝ)
    exact_mod_cast St.p5
  have hP : (0 : ℝ) < P := by linarith
  have ha : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hb : 0 < X.b' := St.bpos
  have hbp : X.b' * P < A := by
    have h1 : P < A / X.b' := St.pab
    rw [lt_div_iff₀ hb] at h1
    linarith
  have hY := St.Y1
  have hk2 : X.k ^ 2 ≤ P := by
    have h1 : X.k ^ 2 * X.Y ^ 2 ≤ P := St.pk
    have hY2 : (1 : ℝ) ≤ X.Y ^ 2 := one_le_pow₀ hY
    have h2 : X.k ^ 2 * 1 ≤ X.k ^ 2 * X.Y ^ 2 := mul_le_mul_of_nonneg_left hY2 (sq_nonneg X.k)
    linarith
  have hN1 : (1 : ℝ) ≤ X.N1 := by exact_mod_cast St.N1pos
  have hk5 : 5 ≤ X.k := by linarith [St.N1k]
  have hkP : 5 * X.k ≤ P := by nlinarith
  have hN2 : (2 : ℝ) ≤ X.N := by exact_mod_cast St.N2
  have hLa1 : 1 ≤ La := St.La1
  have hLaN : 2 * X.N * La ≤ X.k := St.LaN
  have hLa : 4 * La ≤ X.k := by nlinarith
  have hsN : s ≤ X.N1 := by
    show ((segS X.TT j : ℕ) : ℝ) ≤ (X.N1 : ℝ)
    exact_mod_cast (St.segB j).2
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have hs2 : 2 * s ≤ X.k := by linarith [St.N1k]
  have hq1 : 1 ≤ q := by rw [hq]; linarith [(Nat.cast_nonneg X.m : (0 : ℝ) ≤ X.m)]

  have e1 : A / P ^ 2 ≤ A / 25 := div_le_div_of_nonneg_left ha (by norm_num) (by nlinarith)
  have e2 : s * (2 * (X.b' / P)) ≤ A / 25 := by
    rw [show s * (2 * (X.b' / P)) = 2 * s * X.b' / P by ring, div_le_div_iff₀ hP (by norm_num)]
    have f1 := mul_le_mul_of_nonneg_right hs2 hb.le
    have f2 := mul_le_mul_of_nonneg_right hkP hb.le
    have f3 := mul_le_mul_of_nonneg_right hP5 ha
    nlinarith
  have e3 : (La / q + 4 / P ^ 2) * (s * (2 * A / P)) ≤ A / 4 + 4 * A / 125 := by
    have hsA : 0 ≤ s * (2 * A / P) := by positivity
    have g1 : (La / q + 4 / P ^ 2) * (s * (2 * A / P)) ≤ (La + 4 / P ^ 2) * (s * (2 * A / P)) :=
      mul_le_mul_of_nonneg_right (by
        have := div_le_self (show (0 : ℝ) ≤ La by linarith) hq1
        linarith) hsA
    have g2 : (La + 4 / P ^ 2) * (s * (2 * A / P)) = 2 * La * s * A / P + 8 * s * A / P ^ 3 := by
      field_simp
      ring
    have g3 : 2 * La * s * A / P ≤ A / 4 := by
      rw [div_le_div_iff₀ hP (by norm_num)]
      have hm := mul_le_mul hLa hs2 (by positivity) (by linarith)
      have h8 : 8 * (La * s) ≤ P := by
        have e : X.k * X.k = X.k ^ 2 := by ring
        linarith
      have h9 := mul_le_mul_of_nonneg_right h8 ha
      linarith
    have g4 : 8 * s * A / P ^ 3 ≤ 4 * A / 125 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h1 : 8 * s ≤ 4 * P / 5 := by linarith
      have h2 : (25 : ℝ) ≤ P ^ 2 := by
        have := mul_le_mul hP5 hP5 (by norm_num) hP.le
        rw [sq]
        linarith
      have h3 : 8 * s * A * 125 ≤ 100 * P * A := by
        have := mul_le_mul_of_nonneg_right h1 ha
        linarith
      have h4 : 100 * P * A ≤ 4 * A * P ^ 3 := by
        have h5 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * A * P)
        have e : 4 * A * P * P ^ 2 = 4 * A * P ^ 3 := by ring
        linarith
      linarith
    linarith
  have e4 : 2 * (La * X.b' / q) ≤ A / 10 := by
    have g1 : La * X.b' / q ≤ La * X.b' := div_le_self (by positivity) hq1
    have g2 : 20 * (La * X.b') ≤ A := by
      have f1 := mul_le_mul_of_nonneg_right hLa hb.le
      have f2 := mul_le_mul_of_nonneg_right hkP hb.le
      linarith
    linarith
  have hwin := ((St.winA _ (next_mem X.TT j).1).1)
  have hfin : (b.oPlus : ℝ) ≤ (X.aT (segNext X.TT j) : ℝ) := by
    have := hO
    linarith
  unfold segAPlus
  exact_mod_cast hfin

/- English proof (translation)
Conclude with `TransportedAlt.mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc h => oPlusAt_of h.2) thr_std`.
-/
theorem restOPlus : RestOPlus := by
  exact TransportedAlt.mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc h => oPlusAt_of h.2) thr_std

end Formalism.MainNotions.ColumnSystems.Pf
