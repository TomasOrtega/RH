import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedDefs
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementK
import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsNoPrimeToPTorsion
import Formalism.EllipticTorsion.EllipticTorsionProofs.TorInt

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F WeierstrassCurve

namespace ReciprocityTheory.ChartRestriction.L1

namespace ThreeTorsionChord

open Formalism.ELL.FormalGroupPointsTorsion

variable {K : Type} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Establish `hxx : ‖x ^ 2‖ < 1` using `by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx (by norm_num)`. Establish `hl1 : ‖l‖ < 1`. Rewrite using `[hl, norm_div, norm_mul, h2, hy, one_mul, div_one]`. Conclude with `add_lt ((mul_le_of_one three_le).trans_lt hxx) ha`. Establish `hll : ‖l ^ 2‖ < 1` using `by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hl1 (by norm_num)`.

Establish `h1 : ‖x2‖ < 1` using `by rw [hx2]; exact sub_lt (sub_lt hll hx) hx`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `: y2 + y = -(l * (x2 - x))` using `by rw [hy2]; ring`. Rewrite using `[this, norm_neg]`. Conclude with `(mul_le_of_one hl1.le).trans_lt (sub_lt h1 hx)`.
-/
lemma dbl {x y a l x2 y2 : K} (h2 : ‖(2 : K)‖ = 1) (hx : ‖x‖ < 1) (hy : ‖y‖ = 1) (ha : ‖a‖ < 1)
    (hl : l = (3 * x ^ 2 + a) / (2 * y)) (hx2 : x2 = l ^ 2 - x - x)
    (hy2 : y2 = -(l * (x2 - x) + y)) : ‖x2‖ < 1 ∧ ‖y2 + y‖ < 1 := by
  have hxx : ‖x ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx (by norm_num)
  have hl1 : ‖l‖ < 1 := by
    rw [hl, norm_div, norm_mul, h2, hy, one_mul, div_one]
    exact add_lt ((mul_le_of_one three_le).trans_lt hxx) ha
  have hll : ‖l ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hl1 (by norm_num)
  have h1 : ‖x2‖ < 1 := by rw [hx2]; exact sub_lt (sub_lt hll hx) hx
  refine ⟨h1, ?_⟩
  have : y2 + y = -(l * (x2 - x)) := by rw [hy2]; ring
  rw [this, norm_neg]
  exact (mul_le_of_one hl1.le).trans_lt (sub_lt h1 hx)

/- English proof (translation)
Establish `hn : ‖y2 - y‖ = 1`. Establish `: y2 - y = -(2 * y) + (y2 + y)` using `by ring`. Rewrite using `[this, dom (by rw [norm_neg, norm_mul, h2, hy, one_mul]; exact hy2), norm_neg, norm_mul, h2, hy, one_mul]`. Establish `hd : ‖x2 - x‖ < 1` using `sub_lt hx2 hx`. Establish `hd0 : 0 < ‖x2 - x‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hne)`.

Establish `hm1 : 1 < ‖m‖`. Rewrite using `[hm, norm_div, hn]`. Conclude with `(one_lt_div hd0).mpr hd`. Establish `hmm : 1 < ‖m ^ 2‖` using `by rw [norm_pow]; exact one_lt_pow₀ hm1 (by norm_num)`. Establish `: m ^ 2 - x2 - x = m ^ 2 + (-x2 - x)` using `by ring`.

Rewrite using `[this, dom ((sub_lt (by rwa [norm_neg]) hx).trans hmm)]`. Conclude with `hmm`.
-/
lemma chordBig {x y x2 y2 m : K} (h2 : ‖(2 : K)‖ = 1) (hx : ‖x‖ < 1) (hy : ‖y‖ = 1)
    (hx2 : ‖x2‖ < 1) (hy2 : ‖y2 + y‖ < 1) (hne : x2 ≠ x) (hm : m = (y2 - y) / (x2 - x)) :
    1 < ‖m ^ 2 - x2 - x‖ := by
  have hn : ‖y2 - y‖ = 1 := by
    have : y2 - y = -(2 * y) + (y2 + y) := by ring
    rw [this, dom (by rw [norm_neg, norm_mul, h2, hy, one_mul]; exact hy2), norm_neg, norm_mul,
      h2, hy, one_mul]
  have hd : ‖x2 - x‖ < 1 := sub_lt hx2 hx
  have hd0 : 0 < ‖x2 - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hm1 : 1 < ‖m‖ := by
    rw [hm, norm_div, hn]; exact (one_lt_div hd0).mpr hd
  have hmm : 1 < ‖m ^ 2‖ := by rw [norm_pow]; exact one_lt_pow₀ hm1 (by norm_num)
  have : m ^ 2 - x2 - x = m ^ 2 + (-x2 - x) := by ring
  rw [this, dom ((sub_lt (by rwa [norm_neg]) hx).trans hmm)]
  exact hmm

end ThreeTorsionChord

/- English proof (translation)
Establish `h20 : (2 : K) ≠ 0` using `by intro h0; rw [h0, norm_zero] at h2; exact zero_ne_one h2`. Establish `h4 : ‖(4 : K)‖ = 1`. Establish `: (4 : K) = 2 * 2` using `by norm_num`. Rewrite using `[this, norm_mul, h2, one_mul]`. Establish `h27 : ‖(27 : K)‖ = 1`.

Establish `: (27 : K) = 3 * 3 * 3` using `by norm_num`. Rewrite using `[this, norm_mul, norm_mul, h3, one_mul, one_mul]`. Establish `hg3' : ‖g3‖ = 1`. Establish `hc : ‖g2 ^ 3‖ < 1`. Rewrite using `[norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hg2 (by norm_num)`.

Assume the negation of the conclusion as `hne`. Establish `hlt : ‖g3‖ < 1` using `lt_of_le_of_ne hg3 hne`. Establish `: ‖g2 ^ 3 - 27 * g3 ^ 2‖ < 1`. Use `Formalism.ELL.FormalGroupPointsTorsion.sub_lt hc ?_` and prove the remaining obligations. Rewrite using `[norm_mul, h27, one_mul, norm_pow]`.

Conclude with `pow_lt_one₀ (norm_nonneg _) hlt (by norm_num)`. Conclude with `absurd hΔ this.ne`. Establish `ha4 : ‖-g2 / 4‖ < 1` using `by rw [norm_div, norm_neg, h4, div_one]; exact hg2`. Establish `ha6 : ‖-g3 / 4‖ = 1` using `by rw [norm_div, norm_neg, h4, div_one]; exact hg3'`. Establish `hW : Formalism.ELL.IntegralModel (Formalism.L2.Th1.A.shortW g2 g3)`.

Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Formalism.L2.Th1.A.shortW, norm_zero, zero_le_one]`. Conclude with `ha4.le`. Conclude with `ha6.le`. Establish `hD : ‖(Formalism.L2.Th1.A.shortW g2 g3).Δ‖ = 1`. Establish `: (Formalism.L2.Th1.A.shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2`.

Simplify using `only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, Formalism.L2.Th1.A.shortW]`. Establish `h40 : (4 : K) ≠ 0` using `by intro h0; rw [h0, norm_zero] at h4; exact zero_ne_one h4`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hΔ]`.

Establish `hx1` using `(Formalism.ELL.torsionIntegral_of Formalism.ELL.formal_group_points_no_prime_to_p_torsion K _ hW hD n hn x y h hP).1`. Assume the negation of the conclusion as `hne`. Establish `hx : ‖x‖ < 1` using `lt_of_le_of_ne hx1 hne`. Establish `heq : y ^ 2 = -g3 / 4 + (x ^ 3 + -g2 / 4 * x)`. Use `h.1` as an intermediate fact.

Rewrite `this` using `[Affine.equation_iff]`. Simplify using `only [Formalism.L2.Th1.A.shortW] at this`. Take the linear combination `this`. Establish `hy : ‖y‖ = 1`. Establish `hs : ‖x ^ 3 + -g2 / 4 * x‖ < 1`.

Use `Formalism.ELL.FormalGroupPointsTorsion.add_lt ?_ ((Formalism.ELL.FormalGroupPointsTorsion.mul_le_of_one ha4.le).trans_lt hx)` and prove the remaining obligations. Rewrite using `[norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx (by norm_num)`. Establish `: ‖y ^ 2‖ = 1`. Rewrite using `[heq, Formalism.ELL.FormalGroupPointsTorsion.dom (by rw [ha6]; exact hs), ha6]`. Rewrite `this` using `[norm_pow]`.

Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this`. Establish `h2y : ‖2 * y‖ = 1` using `by rw [norm_mul, h2, hy, one_mul]`. Establish `hneg : ∀ u v : K, (Formalism.L2.Th1.A.shortW g2 g3).toAffine.negY u v = -v`. Introduce `u v`. Simplify using `[Affine.negY, Formalism.L2.Th1.A.shortW]`.

Establish `hyne : y ≠ (Formalism.L2.Th1.A.shortW g2 g3).toAffine.negY x y`. Rewrite using `[hneg]`. Introduce `h0`. Establish `: 2 * y = 0` using `by linear_combination h0`. Rewrite `h2y` using `[this, norm_zero]`.

Conclude with `zero_ne_one h2y`. Establish `hxy : ¬(x = x ∧ y = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.negY x y)` using `fun hh => hyne hh.2`. Establish `hE : Formalism.ELL.InFormalGroupPoints (3 • Affine.Point.some x y h)`. Establish `e3 : 3 • Affine.Point.some x y h = (Affine.Point.some x y h + Affine.Point.some x y h) + Affine.Point.some x y h`. Rewrite using `[succ_nsmul, two_nsmul]`.

Rewrite using `[e3, Affine.Point.add_some hxy]`. Take `⟨l, hl⟩ : ∃ l, l = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.slope x x y y` from `⟨_, rfl⟩`. Establish `hl' : l = (3 * x ^ 2 + -g2 / 4) / (2 * y)`. Rewrite using `[hl, Affine.slope_of_Y_ne rfl hyne, hneg]`. Simplify using `only [Formalism.L2.Th1.A.shortW]`.

Apply the tactic sequence `congr 1 <;> ring`. Take `⟨x2, hx2⟩ : ∃ x2, x2 = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.addX x x l` from `⟨_, rfl⟩`. Take `⟨y2, hy2⟩ : ∃ y2, y2 = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.addY x x y l` from `⟨_, rfl⟩`. Establish `hx2' : x2 = l ^ 2 - x - x`. Rewrite using `[hx2]`.

Simplify using `only [Affine.addX, Formalism.L2.Th1.A.shortW]`. Expand and normalize the polynomial expressions, which then agree. Establish `hy2' : y2 = -(l * (x2 - x) + y)`. Rewrite using `[hy2, Affine.addY, hneg, Affine.negAddY, ← hx2]`. Take `⟨hX2, hY2⟩` from `ThreeTorsionChord.dbl h2 hx hy ha4 hl' hx2' hy2'`.

Simplify using `only [← hl, ← hx2, ← hy2]`. Distinguish the cases in `hc : x2 = x ∧ y2 = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.negY x y`. Rewrite using `[Affine.Point.add_of_Y_eq hc.1 hc.2, Affine.Point.zero_def]`. Discharge the goal by the elementary cases of `trivial`. Rewrite using `[Affine.Point.add_some hc]`.

Establish `hxne : x2 ≠ x`. Introduce `hxe`. Establish `hq : (Formalism.L2.Th1.A.shortW g2 g3).toAffine.Equation x2 y2`. Rewrite using `[hx2, hy2, hl]`. Conclude with `(Affine.nonsingular_add h h hxy).1`.

Establish `hye` using `Affine.Y_eq_of_Y_ne hq h.1 hxe (fun hh => hc ⟨hxe, hh⟩)`. Rewrite `hY2` using `[hye, ← two_mul, h2y]`. Conclude with `lt_irrefl _ hY2`. Establish `hb` using `ThreeTorsionChord.chordBig h2 hx hy hX2 hY2 hxne rfl`. Use `show 1 < ‖(Formalism.L2.Th1.A.shortW g2 g3).toAffine.addX x2 x _‖`.

Rewrite using `[Affine.slope_of_X_ne hxne]`. Simplify using `only [Affine.addX, Formalism.L2.Th1.A.shortW]`. Use `hb using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `h3P : 3 • Affine.Point.some x y h = 0`.

Use `Formalism.ELL.formal_group_points_no_prime_to_p_torsion K _ hW hD n hn _ hE ?_` and prove the remaining obligations. Rewrite using `[smul_comm, hP, smul_zero]`. Establish `hd1 : addOrderOf (Affine.Point.some x y h) ∣ 3` using `addOrderOf_dvd_of_nsmul_eq_zero h3P`. Establish `hd2 : addOrderOf (Affine.Point.some x y h) ∣ n` using `addOrderOf_dvd_of_nsmul_eq_zero hP`. Establish `hcop : Nat.Coprime 3 n` using `(Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hen`.

Establish `h1 : addOrderOf (Affine.Point.some x y h) = 1` using `Nat.eq_one_of_dvd_coprimes hcop hd1 hd2`. Conclude with `Affine.Point.some_ne_zero h (AddMonoid.addOrderOf_eq_one_iff.mp h1)`.
-/
theorem torsUnit3 (K : Type) [NormedField K] [IsUltrametricDist K] (g2 g3 : K) (h2 : ‖(2 : K)‖ = 1)
    (h3 : ‖(3 : K)‖ = 1) (hg2 : ‖g2‖ < 1) (hg3 : ‖g3‖ ≤ 1) (hΔ : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1)
    (n : ℕ) (hn : ‖(n : K)‖ = 1) (hen : ¬ 3 ∣ n) (x y : K)
    (h : (Formalism.L2.Th1.A.shortW g2 g3).toAffine.Nonsingular x y) (hP : n • (Affine.Point.some x y h) = 0) : ‖x‖ = 1 := by
  have h20 : (2 : K) ≠ 0 := by intro h0; rw [h0, norm_zero] at h2; exact zero_ne_one h2
  have h4 : ‖(4 : K)‖ = 1 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this, norm_mul, h2, one_mul]
  have h27 : ‖(27 : K)‖ = 1 := by
    have : (27 : K) = 3 * 3 * 3 := by norm_num
    rw [this, norm_mul, norm_mul, h3, one_mul, one_mul]
  have hg3' : ‖g3‖ = 1 := by
    have hc : ‖g2 ^ 3‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hg2 (by norm_num)
    by_contra hne
    have hlt : ‖g3‖ < 1 := lt_of_le_of_ne hg3 hne
    have : ‖g2 ^ 3 - 27 * g3 ^ 2‖ < 1 := by
      refine Formalism.ELL.FormalGroupPointsTorsion.sub_lt hc ?_
      rw [norm_mul, h27, one_mul, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hlt (by norm_num)
    exact absurd hΔ this.ne
  have ha4 : ‖-g2 / 4‖ < 1 := by rw [norm_div, norm_neg, h4, div_one]; exact hg2
  have ha6 : ‖-g3 / 4‖ = 1 := by rw [norm_div, norm_neg, h4, div_one]; exact hg3'
  have hW : Formalism.ELL.IntegralModel (Formalism.L2.Th1.A.shortW g2 g3) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Formalism.L2.Th1.A.shortW, norm_zero, zero_le_one]
    · exact ha4.le
    · exact ha6.le
  have hD : ‖(Formalism.L2.Th1.A.shortW g2 g3).Δ‖ = 1 := by
    have : (Formalism.L2.Th1.A.shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2 := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
        WeierstrassCurve.b₈, Formalism.L2.Th1.A.shortW]
      have h40 : (4 : K) ≠ 0 := by intro h0; rw [h0, norm_zero] at h4; exact zero_ne_one h4
      field_simp
      ring
    rw [this, hΔ]
  have hx1 := (Formalism.ELL.torsionIntegral_of Formalism.ELL.formal_group_points_no_prime_to_p_torsion K _ hW hD n hn x y h hP).1
  by_contra hne
  have hx : ‖x‖ < 1 := lt_of_le_of_ne hx1 hne
  have heq : y ^ 2 = -g3 / 4 + (x ^ 3 + -g2 / 4 * x) := by
    have := h.1
    rw [Affine.equation_iff] at this
    simp only [Formalism.L2.Th1.A.shortW] at this
    linear_combination this
  have hy : ‖y‖ = 1 := by
    have hs : ‖x ^ 3 + -g2 / 4 * x‖ < 1 := by
      refine Formalism.ELL.FormalGroupPointsTorsion.add_lt ?_ ((Formalism.ELL.FormalGroupPointsTorsion.mul_le_of_one ha4.le).trans_lt hx)
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx (by norm_num)
    have : ‖y ^ 2‖ = 1 := by
      rw [heq, Formalism.ELL.FormalGroupPointsTorsion.dom (by rw [ha6]; exact hs), ha6]
    rw [norm_pow] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
  have h2y : ‖2 * y‖ = 1 := by rw [norm_mul, h2, hy, one_mul]
  have hneg : ∀ u v : K, (Formalism.L2.Th1.A.shortW g2 g3).toAffine.negY u v = -v := by
    intro u v; simp [Affine.negY, Formalism.L2.Th1.A.shortW]
  have hyne : y ≠ (Formalism.L2.Th1.A.shortW g2 g3).toAffine.negY x y := by
    rw [hneg]; intro h0
    have : 2 * y = 0 := by linear_combination h0
    rw [this, norm_zero] at h2y; exact zero_ne_one h2y
  have hxy : ¬(x = x ∧ y = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.negY x y) := fun hh => hyne hh.2

  have hE : Formalism.ELL.InFormalGroupPoints (3 • Affine.Point.some x y h) := by
    have e3 : 3 • Affine.Point.some x y h =
        (Affine.Point.some x y h + Affine.Point.some x y h) + Affine.Point.some x y h := by
      rw [succ_nsmul, two_nsmul]
    rw [e3, Affine.Point.add_some hxy]
    obtain ⟨l, hl⟩ : ∃ l, l = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.slope x x y y := ⟨_, rfl⟩
    have hl' : l = (3 * x ^ 2 + -g2 / 4) / (2 * y) := by
      rw [hl, Affine.slope_of_Y_ne rfl hyne, hneg]
      simp only [Formalism.L2.Th1.A.shortW]
      congr 1 <;> ring
    obtain ⟨x2, hx2⟩ : ∃ x2, x2 = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.addX x x l := ⟨_, rfl⟩
    obtain ⟨y2, hy2⟩ : ∃ y2, y2 = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.addY x x y l := ⟨_, rfl⟩
    have hx2' : x2 = l ^ 2 - x - x := by
      rw [hx2]; simp only [Affine.addX, Formalism.L2.Th1.A.shortW]; ring
    have hy2' : y2 = -(l * (x2 - x) + y) := by
      rw [hy2, Affine.addY, hneg, Affine.negAddY, ← hx2]
    obtain ⟨hX2, hY2⟩ := ThreeTorsionChord.dbl h2 hx hy ha4 hl' hx2' hy2'
    simp only [← hl, ← hx2, ← hy2]
    by_cases hc : x2 = x ∧ y2 = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.negY x y
    · rw [Affine.Point.add_of_Y_eq hc.1 hc.2, Affine.Point.zero_def]; trivial
    · rw [Affine.Point.add_some hc]
      have hxne : x2 ≠ x := by
        intro hxe
        have hq : (Formalism.L2.Th1.A.shortW g2 g3).toAffine.Equation x2 y2 := by
          rw [hx2, hy2, hl]; exact (Affine.nonsingular_add h h hxy).1
        have hye := Affine.Y_eq_of_Y_ne hq h.1 hxe (fun hh => hc ⟨hxe, hh⟩)
        rw [hye, ← two_mul, h2y] at hY2
        exact lt_irrefl _ hY2
      have hb := ThreeTorsionChord.chordBig h2 hx hy hX2 hY2 hxne rfl
      show 1 < ‖(Formalism.L2.Th1.A.shortW g2 g3).toAffine.addX x2 x _‖
      rw [Affine.slope_of_X_ne hxne]
      simp only [Affine.addX, Formalism.L2.Th1.A.shortW]
      convert hb using 2
      ring
  have h3P : 3 • Affine.Point.some x y h = 0 := by
    refine Formalism.ELL.formal_group_points_no_prime_to_p_torsion K _ hW hD n hn _ hE ?_
    rw [smul_comm, hP, smul_zero]
  have hd1 : addOrderOf (Affine.Point.some x y h) ∣ 3 := addOrderOf_dvd_of_nsmul_eq_zero h3P
  have hd2 : addOrderOf (Affine.Point.some x y h) ∣ n := addOrderOf_dvd_of_nsmul_eq_zero hP
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hen
  have h1 : addOrderOf (Affine.Point.some x y h) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  exact Affine.Point.some_ne_zero h (AddMonoid.addOrderOf_eq_one_iff.mp h1)

end ReciprocityTheory.ChartRestriction.L1
