import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementK

noncomputable section

namespace Formalism.L2.Th1.B.KNorm

open Formalism.ELL (InFormalGroupPoints)
open Formalism.L2.Th1.E (px py IntCurve)
open WeierstrassCurve.Affine (Point)

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
The claim follows from `(IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)`.
-/
lemma nadd_le {a b : K} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a + b‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

/- English proof (translation)
The claim follows from `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)`.
-/
lemma nadd_lt {a b : K} {r : ℝ} (ha : ‖a‖ < r) (hb : ‖b‖ < r) : ‖a + b‖ < r :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `nadd_le ha (by rwa [norm_neg])`.
-/
lemma nsub_le {a b : K} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a - b‖ ≤ r := by
  rw [sub_eq_add_neg]
  exact nadd_le ha (by rwa [norm_neg])

/- English proof (translation)
Rewrite using `[IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]`.
-/
lemma ndom {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

/- English proof (translation)
Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ ha (norm_nonneg _) hb`.
-/
lemma nmul1 {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hb

/- English proof (translation)
Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) ha`.
-/
lemma npow1 {a : K} (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a ^ n‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) ha

/- English proof (translation)
Rewrite using `[show (2 : K) = 1 + 1 by norm_num]`. Conclude with `nadd_le norm_one.le norm_one.le`.
-/
lemma n2le : ‖(2 : K)‖ ≤ 1 := by
  rw [show (2 : K) = 1 + 1 by norm_num]
  exact nadd_le norm_one.le norm_one.le

/- English proof (translation)
Rewrite using `[show (4 : K) = 2 * 2 by norm_num]`. Conclude with `nmul1 n2le n2le`.
-/
lemma n4le : ‖(4 : K)‖ ≤ 1 := by
  rw [show (4 : K) = 2 * 2 by norm_num]
  exact nmul1 n2le n2le

/- English proof (translation)
Rewrite using `[show (4 : K) = 2 * 2 by norm_num, norm_mul, h2]`. Evaluate the numerical expressions.
-/
lemma n4 (h2 : ‖(2 : K)‖ = 2⁻¹) : ‖(4 : K)‖ = 4⁻¹ := by
  rw [show (4 : K) = 2 * 2 by norm_num, norm_mul, h2]
  norm_num

/- English proof (translation)
Rewrite using `[show (3 : K) = 1 + 2 by norm_num, ndom (by rw [h2, norm_one]; norm_num), norm_one]`.
-/
lemma n3 (h2 : ‖(2 : K)‖ = 2⁻¹) : ‖(3 : K)‖ = 1 := by
  rw [show (3 : K) = 1 + 2 by norm_num, ndom (by rw [h2, norm_one]; norm_num), norm_one]

/- English proof (translation)
Introduce `h`. Rewrite `h2` using `[h, norm_zero]`. Evaluate the numerical expressions using `at h2`.
-/
lemma two_ne (h2 : ‖(2 : K)‖ = 2⁻¹) : (2 : K) ≠ 0 := by
  intro h
  rw [h, norm_zero] at h2
  norm_num at h2

/- English proof (translation)
Simplify using `only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]`. Use `⟨nadd_le (npow1 h1 2) (nmul1 n4le h2), nadd_le (nmul1 n2le h4) (nmul1 h1 h3), nadd_le (npow1 h3 2) (nmul1 n4le h6), ?_⟩` and prove the remaining obligations. Conclude with `nsub_le (nadd_le (nsub_le (nadd_le (nmul1 (npow1 h1 2) h6) (nmul1 (nmul1 n4le h2) h6)) (nmul1 (nmul1 h1 h3) h4)) (nmul1 h2 (npow1 h3 2))) (npow1 h4 2)`.
-/
lemma b_int (W : WeierstrassCurve K) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1)
    (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) :
    ‖W.b₂‖ ≤ 1 ∧ ‖W.b₄‖ ≤ 1 ∧ ‖W.b₆‖ ≤ 1 ∧ ‖W.b₈‖ ≤ 1 := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  refine ⟨nadd_le (npow1 h1 2) (nmul1 n4le h2), nadd_le (nmul1 n2le h4) (nmul1 h1 h3),
    nadd_le (npow1 h3 2) (nmul1 n4le h6), ?_⟩
  exact nsub_le (nadd_le (nsub_le (nadd_le (nmul1 (npow1 h1 2) h6) (nmul1 (nmul1 n4le h2) h6))
    (nmul1 (nmul1 h1 h3) h4)) (nmul1 h2 (npow1 h3 2))) (npow1 h4 2)

/- English proof (translation)
Rewrite using `[norm_mul, norm_pow, n4 h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma t4 (h2 : ‖(2 : K)‖ = 2⁻¹) (x : K) : ‖4 * x ^ 3‖ = ‖x‖ ^ 3 / 4 := by
  rw [norm_mul, norm_pow, n4 h2]
  ring

/- English proof (translation)
Rewrite using `[norm_mul, norm_pow]`. Conclude with `mul_le_of_le_one_left (by positivity) hb`.
-/
lemma tb2 {b : K} (hb : ‖b‖ ≤ 1) (x : K) : ‖b * x ^ 2‖ ≤ ‖x‖ ^ 2 := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) hb

/- English proof (translation)
Rewrite using `[norm_mul, norm_mul, h2]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hb (norm_nonneg x)]`.
-/
lemma tb4 (h2 : ‖(2 : K)‖ = 2⁻¹) {b : K} (hb : ‖b‖ ≤ 1) (x : K) : ‖2 * b * x‖ ≤ ‖x‖ / 2 := by
  rw [norm_mul, norm_mul, h2]
  nlinarith [mul_le_mul_of_nonneg_right hb (norm_nonneg x)]

variable {b2 b4 b6 b8 x : K}

/- English proof (translation)
Establish `r0 : 0 ≤ ‖x‖` using `norm_nonneg _`. Establish `e1 : ‖x‖ ^ 2 ≤ ‖x‖ ^ 3 / 4` using `by nlinarith [mul_nonneg (sq_nonneg ‖x‖) (sub_nonneg.2 hx)]`. Establish `e2 : ‖x‖ / 2 ≤ ‖x‖ ^ 3 / 4` using `by nlinarith [mul_nonneg r0 (sub_nonneg.2 hx)]`. Establish `e3 : 1 ≤ ‖x‖ ^ 3 / 4` using `by nlinarith [pow_le_pow_left₀ (by norm_num) hx 3]`. Conclude with `nadd_le (nadd_le (nadd_le (t4 h2 x).le ((tb2 hb2 x).trans e1)) ((tb4 h2 hb4 x).trans e2)) (hb6.trans e3)`.
-/
lemma psi_le (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ ≤ 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (hx : 4 ≤ ‖x‖) : ‖4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6‖ ≤ ‖x‖ ^ 3 / 4 := by
  have r0 : 0 ≤ ‖x‖ := norm_nonneg _
  have e1 : ‖x‖ ^ 2 ≤ ‖x‖ ^ 3 / 4 := by nlinarith [mul_nonneg (sq_nonneg ‖x‖) (sub_nonneg.2 hx)]
  have e2 : ‖x‖ / 2 ≤ ‖x‖ ^ 3 / 4 := by nlinarith [mul_nonneg r0 (sub_nonneg.2 hx)]
  have e3 : 1 ≤ ‖x‖ ^ 3 / 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) hx 3]
  exact nadd_le (nadd_le (nadd_le (t4 h2 x).le ((tb2 hb2 x).trans e1)) ((tb4 h2 hb4 x).trans e2))
    (hb6.trans e3)

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `r0 : 0 ≤ ‖x‖` using `norm_nonneg _`. Establish `e1 : ‖x‖ ^ 2 < ‖x‖ ^ 3 / 4` using `by nlinarith [mul_pos (pow_pos (by linarith : (0:ℝ) < ‖x‖) 2) (sub_pos.2 hlt)]`. Establish `e2 : ‖x‖ / 2 < ‖x‖ ^ 3 / 4` using `by nlinarith [mul_pos (by linarith : (0:ℝ) < ‖x‖) (sub_pos.2 hlt)]`.

Establish `e3 : 1 < ‖x‖ ^ 3 / 4` using `by nlinarith [pow_le_pow_left₀ (by norm_num) hlt.le 3]`. Establish `hr : ‖b2 * x ^ 2 + 2 * b4 * x + b6‖ < ‖4 * x ^ 3‖`. Rewrite using `[t4 h2]`. Conclude with `nadd_lt (nadd_lt ((tb2 hb2 x).trans_lt e1) ((tb4 h2 hb4 x).trans_lt e2)) (hb6.trans_lt e3)`. Establish `key` using `ndom hr`.

Rewrite `key` using `[show 4 * x ^ 3 + (b2 * x ^ 2 + 2 * b4 * x + b6) = 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 by ring, h0, norm_zero, t4 h2]`. Use polynomial arithmetic with `[pow_pos (by linarith : (0:ℝ) < ‖x‖) 3]`.
-/
lemma psi_zero_le (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ ≤ 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (h0 : 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0) : ‖x‖ ≤ 4 := by
  by_contra hlt
  push_neg at hlt
  have r0 : 0 ≤ ‖x‖ := norm_nonneg _
  have e1 : ‖x‖ ^ 2 < ‖x‖ ^ 3 / 4 := by nlinarith [mul_pos (pow_pos (by linarith : (0:ℝ) < ‖x‖) 2) (sub_pos.2 hlt)]
  have e2 : ‖x‖ / 2 < ‖x‖ ^ 3 / 4 := by nlinarith [mul_pos (by linarith : (0:ℝ) < ‖x‖) (sub_pos.2 hlt)]
  have e3 : 1 < ‖x‖ ^ 3 / 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) hlt.le 3]
  have hr : ‖b2 * x ^ 2 + 2 * b4 * x + b6‖ < ‖4 * x ^ 3‖ := by
    rw [t4 h2]
    exact nadd_lt (nadd_lt ((tb2 hb2 x).trans_lt e1) ((tb4 h2 hb4 x).trans_lt e2)) (hb6.trans_lt e3)
  have key := ndom hr
  rw [show 4 * x ^ 3 + (b2 * x ^ 2 + 2 * b4 * x + b6) = 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 by ring,
    h0, norm_zero, t4 h2] at key
  nlinarith [pow_pos (by linarith : (0:ℝ) < ‖x‖) 3]

/- English proof (translation)
Establish `r0 : 0 ≤ ‖x‖` using `norm_nonneg _`. Establish `r2 : 16 ≤ ‖x‖ ^ 2` using `by nlinarith`. Establish `r4 : ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2` using `by ring`. Establish `e1 : ‖x‖ ^ 2 < ‖x‖ ^ 4` using `by rw [r4]; nlinarith`. Establish `e2 : ‖x‖ / 2 < ‖x‖ ^ 4` using `by rw [r4]; nlinarith`.

Establish `e3 : 1 < ‖x‖ ^ 4` using `by rw [r4]; nlinarith`. Rewrite using `[show x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8 = x ^ 4 + -(b4 * x ^ 2 + 2 * b6 * x + b8) by ring]`. Rewrite using `[ndom, norm_pow]`. Rewrite using `[norm_neg, norm_pow]`. Conclude with `nadd_lt (nadd_lt ((tb2 hb4 x).trans_lt e1) ((tb4 h2 hb6 x).trans_lt e2)) (hb8.trans_lt e3)`.
-/
lemma num_norm (h2 : ‖(2 : K)‖ = 2⁻¹) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1) (hb8 : ‖b8‖ ≤ 1)
    (hx : 4 ≤ ‖x‖) : ‖x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8‖ = ‖x‖ ^ 4 := by
  have r0 : 0 ≤ ‖x‖ := norm_nonneg _
  have r2 : 16 ≤ ‖x‖ ^ 2 := by nlinarith
  have r4 : ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 := by ring
  have e1 : ‖x‖ ^ 2 < ‖x‖ ^ 4 := by rw [r4]; nlinarith
  have e2 : ‖x‖ / 2 < ‖x‖ ^ 4 := by rw [r4]; nlinarith
  have e3 : 1 < ‖x‖ ^ 4 := by rw [r4]; nlinarith
  rw [show x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8 = x ^ 4 + -(b4 * x ^ 2 + 2 * b6 * x + b8) by ring]
  rw [ndom, norm_pow]
  rw [norm_neg, norm_pow]
  exact nadd_lt (nadd_lt ((tb2 hb4 x).trans_lt e1) ((tb4 h2 hb6 x).trans_lt e2)) (hb8.trans_lt e3)

/- English proof (translation)
Establish `hn` using `num_norm h2 hb4 hb6 hb8 hx`. Establish `hp` using `psi_le h2 hb2 hb4 hb6 hx`. Establish `hm` using `congrArg norm hX`. Rewrite `hm` using `[norm_mul, hn]`. Assume the negation of the conclusion as `hle`.

Use `push_neg at hle`. Establish `hb : ‖X‖ * ‖4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6‖ ≤ 4 * (‖x‖ ^ 3 / 4)` using `mul_le_mul hle hp (norm_nonneg _) (by norm_num)`. Establish `r3 : 0 < ‖x‖ ^ 3` using `pow_pos (by linarith) 3`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma dup_core (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ ≤ 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (hb8 : ‖b8‖ ≤ 1) (hx : 4 ≤ ‖x‖) {X : K}
    (hX : X * (4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6)
      = x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8) : 4 < ‖X‖ := by
  have hn := num_norm h2 hb4 hb6 hb8 hx
  have hp := psi_le h2 hb2 hb4 hb6 hx
  have hm := congrArg norm hX
  rw [norm_mul, hn] at hm
  by_contra hle
  push_neg at hle
  have hb : ‖X‖ * ‖4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6‖ ≤ 4 * (‖x‖ ^ 3 / 4) :=
    mul_le_mul hle hp (norm_nonneg _) (by norm_num)
  have r3 : 0 < ‖x‖ ^ 3 := pow_pos (by linarith) 3
  nlinarith

/- English proof (translation)
Use `le_antisymm (psi_zero_le h2 hb2.le hb4 hb6 h0) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `e1 : ‖x‖ ^ 3 / 4 < ‖x‖ ^ 2` using `by nlinarith [mul_pos (pow_pos (by linarith : (0:ℝ) < ‖x‖) 2) (sub_pos.2 hlt)]`. Establish `e2 : ‖x‖ / 2 < ‖x‖ ^ 2` using `by nlinarith`.

Establish `e3 : 1 < ‖x‖ ^ 2` using `by nlinarith`. Establish `hd : ‖b2 * x ^ 2‖ = ‖x‖ ^ 2` using `by rw [norm_mul, hb2, one_mul, norm_pow]`. Establish `hr : ‖4 * x ^ 3 + 2 * b4 * x + b6‖ < ‖b2 * x ^ 2‖`. Rewrite using `[hd]`. Conclude with `nadd_lt (nadd_lt ((t4 h2 x).trans_lt e1) ((tb4 h2 hb4 x).trans_lt e2)) (hb6.trans_lt e3)`.

Establish `key` using `ndom hr`. Rewrite `key` using `[show b2 * x ^ 2 + (4 * x ^ 3 + 2 * b4 * x + b6) = 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 by ring, h0, norm_zero, hd]`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma psi_zero_eq (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ = 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (hx : 1 < ‖x‖) (h0 : 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0) : ‖x‖ = 4 := by
  refine le_antisymm (psi_zero_le h2 hb2.le hb4 hb6 h0) ?_
  by_contra hlt
  push_neg at hlt
  have e1 : ‖x‖ ^ 3 / 4 < ‖x‖ ^ 2 := by nlinarith [mul_pos (pow_pos (by linarith : (0:ℝ) < ‖x‖) 2) (sub_pos.2 hlt)]
  have e2 : ‖x‖ / 2 < ‖x‖ ^ 2 := by nlinarith
  have e3 : 1 < ‖x‖ ^ 2 := by nlinarith
  have hd : ‖b2 * x ^ 2‖ = ‖x‖ ^ 2 := by rw [norm_mul, hb2, one_mul, norm_pow]
  have hr : ‖4 * x ^ 3 + 2 * b4 * x + b6‖ < ‖b2 * x ^ 2‖ := by
    rw [hd]
    exact nadd_lt (nadd_lt ((t4 h2 x).trans_lt e1) ((tb4 h2 hb4 x).trans_lt e2)) (hb6.trans_lt e3)
  have key := ndom hr
  rw [show b2 * x ^ 2 + (4 * x ^ 3 + 2 * b4 * x + b6) = 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 by ring,
    h0, norm_zero, hd] at key
  nlinarith

/- English proof (translation)
Establish `e : x ^ 2 * (4 * x + b2) = -(2 * b4 * x + b6)` using `by linear_combination h0`. Establish `hr : ‖2 * b4 * x + b6‖ ≤ 2` using `nadd_le ((tb4 h2 hb4 x).trans (by rw [hx]; norm_num)) (hb6.trans (by norm_num))`. Establish `hm` using `congrArg norm e`. Rewrite `hm` using `[norm_mul, norm_pow, hx, norm_neg]`. Use polynomial arithmetic with `[norm_nonneg (4 * x + b2)]`.
-/
lemma four_add_le (h2 : ‖(2 : K)‖ = 2⁻¹) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (hx : ‖x‖ = 4) (h0 : 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0) :
    ‖4 * x + b2‖ ≤ 1 / 8 := by
  have e : x ^ 2 * (4 * x + b2) = -(2 * b4 * x + b6) := by linear_combination h0
  have hr : ‖2 * b4 * x + b6‖ ≤ 2 :=
    nadd_le ((tb4 h2 hb4 x).trans (by rw [hx]; norm_num)) (hb6.trans (by norm_num))
  have hm := congrArg norm e
  rw [norm_mul, norm_pow, hx, norm_neg] at hm
  nlinarith [norm_nonneg (4 * x + b2)]

/- English proof (translation)
Establish `f` using `four_add_le h2 hb4 hb6 hx h0`. Establish `f'` using `four_add_le h2 hb4 hb6 hx' h0'`. Establish `hfac : (x - x') * (4 * x * x' + (x * (4 * x + b2) + x' * (4 * x' + b2) + 2 * b4)) = 0`. Take the linear combination `h0 - h0'`. Break down `mul_eq_zero.1 hfac with h | h` into its components or cases.

Conclude with `sub_eq_zero.1 h`. It suffices to derive a contradiction. Establish `hdom : ‖4 * x * x'‖ = 4`. Rewrite using `[norm_mul, norm_mul, n4 h2, hx, hx']`. Evaluate the numerical expressions.

Establish `a1 : ‖x * (4 * x + b2)‖ < 4`. Rewrite using `[norm_mul, hx]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `a2 : ‖x' * (4 * x' + b2)‖ < 4`. Rewrite using `[norm_mul, hx']`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `a3 : ‖2 * b4‖ < 4`. Rewrite using `[norm_mul, h2]`. Use polynomial arithmetic with `[norm_nonneg b4]`. Establish `hr : ‖x * (4 * x + b2) + x' * (4 * x' + b2) + 2 * b4‖ < ‖4 * x * x'‖`.

Rewrite using `[hdom]`. Conclude with `nadd_lt (nadd_lt a1 a2) a3`. Establish `key` using `ndom hr`. Rewrite `key` using `[h, norm_zero, hdom]`. Evaluate the numerical expressions using `at key`.
-/
lemma psi_zero_unique (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ ≤ 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    {x' : K} (hx : ‖x‖ = 4) (hx' : ‖x'‖ = 4)
    (h0 : 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0)
    (h0' : 4 * x' ^ 3 + b2 * x' ^ 2 + 2 * b4 * x' + b6 = 0) : x = x' := by
  have f := four_add_le h2 hb4 hb6 hx h0
  have f' := four_add_le h2 hb4 hb6 hx' h0'
  have hfac : (x - x') * (4 * x * x' + (x * (4 * x + b2) + x' * (4 * x' + b2) + 2 * b4)) = 0 := by
    linear_combination h0 - h0'
  rcases mul_eq_zero.1 hfac with h | h
  · exact sub_eq_zero.1 h
  exfalso
  have hdom : ‖4 * x * x'‖ = 4 := by
    rw [norm_mul, norm_mul, n4 h2, hx, hx']
    norm_num
  have a1 : ‖x * (4 * x + b2)‖ < 4 := by
    rw [norm_mul, hx]
    linarith
  have a2 : ‖x' * (4 * x' + b2)‖ < 4 := by
    rw [norm_mul, hx']
    linarith
  have a3 : ‖2 * b4‖ < 4 := by
    rw [norm_mul, h2]
    nlinarith [norm_nonneg b4]
  have hr : ‖x * (4 * x + b2) + x' * (4 * x' + b2) + 2 * b4‖ < ‖4 * x * x'‖ := by
    rw [hdom]
    exact nadd_lt (nadd_lt a1 a2) a3
  have key := ndom hr
  rw [h, norm_zero, hdom] at key
  norm_num at key

end Norm

section Curve

variable {K : Type} [Field K] {W : WeierstrassCurve K} {x y : K}

/- English proof (translation)
Rewrite `h` using `[WeierstrassCurve.Affine.equation_iff]`. Simplify using `only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]`. Take the linear combination `4 * h`.
-/
lemma psi_eq (h : W.toAffine.Equation x y) :
    (2 * y + W.a₁ * x + W.a₃) ^ 2 = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination 4 * h

/- English proof (translation)
Rewrite using `[WeierstrassCurve.Affine.negY]`. Apply the tactic sequence `constructor <;> intro h <;> linear_combination h`.
-/
lemma negY_iff : y = W.toAffine.negY x y ↔ 2 * y + W.a₁ * x + W.a₃ = 0 := by
  rw [WeierstrassCurve.Affine.negY]
  constructor <;> intro h <;> linear_combination h

variable [DecidableEq K]

/- English proof (translation)
Establish `hden : y - W.toAffine.negY x y ≠ 0` using `sub_ne_zero.2 hy`. Establish `hdd : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃`. Rewrite using `[WeierstrassCurve.Affine.negY]`. Expand and normalize the polynomial expressions, which then agree. Establish `hl : W.toAffine.slope x x y y * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y`.

Rewrite using `[WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, ← hdd, div_mul_cancel₀ _ hden]`. Rewrite using `[← psi_eq h, WeierstrassCurve.Affine.addX]`. Rewrite `h` using `[WeierstrassCurve.Affine.equation_iff]`. Simplify using `only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]`. Take the linear combination `(W.toAffine.slope x x y y * (2 * y + W.a₁ * x + W.a₃) + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) + W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * hl + (-(W.a₁ ^ 2 + 4 * W.a₂ + 8 * x)) * h`.
-/
lemma dup (h : W.toAffine.Equation x y) (hy : y ≠ W.toAffine.negY x y) :
    W.toAffine.addX x x (W.toAffine.slope x x y y)
        * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
      = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
  have hden : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.2 hy
  have hdd : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
    rw [WeierstrassCurve.Affine.negY]
    ring
  have hl : W.toAffine.slope x x y y * (2 * y + W.a₁ * x + W.a₃)
      = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, ← hdd, div_mul_cancel₀ _ hden]
  rw [← psi_eq h, WeierstrassCurve.Affine.addX]
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination (W.toAffine.slope x x y y * (2 * y + W.a₁ * x + W.a₃)
      + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) + W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * hl
    + (-(W.a₁ ^ 2 + 4 * W.a₂ + 8 * x)) * h

/- English proof (translation)
Rewrite using `[add_eq_zero_iff_eq_neg, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]`. Simplify using `only [true_and]`. Conclude with `negY_iff`.
-/
lemma add_self_iff (h : W.toAffine.Nonsingular x y) :
    (Point.some x y h + Point.some x y h = 0) ↔ 2 * y + W.a₁ * x + W.a₃ = 0 := by
  rw [add_eq_zero_iff_eq_neg, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
  simp only [true_and]
  exact negY_iff

/- English proof (translation)
Rewrite using `[WeierstrassCurve.Affine.Point.add_some (fun hxy => hy hxy.2)]`. Both sides reduce to the same expression.
-/
lemma px_add_self (h : W.toAffine.Nonsingular x y) (hy : y ≠ W.toAffine.negY x y) :
    px W (Point.some x y h + Point.some x y h)
      = W.toAffine.addX x x (W.toAffine.slope x x y y) := by
  rw [WeierstrassCurve.Affine.Point.add_some (fun hxy => hy hxy.2)]
  rfl

end Curve

section Main

variable {K : Type} [NormedField K] [IsUltrametricDist K] [DecidableEq K]
  {W : WeierstrassCurve K}

/- English proof (translation)
Take `⟨h1, h2a, h3, h4, h6, -⟩` from `hW`. Take `⟨hb2, hb4, hb6, -⟩` from `b_int W h1 h2a h3 h4 h6`. Consider the cases of `P with`. Consider the case `zero`. Express the relevant statement in the definitionally equal form `‖(0 : K)‖ ≤ 4`.

Rewrite using `[norm_zero]`. Evaluate the numerical expressions. Consider the case `some x y h`. Establish `hd` using `(add_self_iff h).1 hP`. Establish `h0` using `psi_eq h.1`.

Rewrite `h0` using `[hd]`. Conclude with `psi_zero_le (x := x) h2 hb2 hb4 hb6 (by rw [← h0]; ring)`.
-/
lemma two_tors_le (hW : IntCurve W) (h2 : ‖(2 : K)‖ = 2⁻¹) (P : W.toAffine.Point)
    (hP : P + P = 0) : ‖px W P‖ ≤ 4 := by
  obtain ⟨h1, h2a, h3, h4, h6, -⟩ := hW
  obtain ⟨hb2, hb4, hb6, -⟩ := b_int W h1 h2a h3 h4 h6
  cases P with
  | zero =>
    change ‖(0 : K)‖ ≤ 4
    rw [norm_zero]
    norm_num
  | some x y h =>
    have hd := (add_self_iff h).1 hP
    have h0 := psi_eq h.1
    rw [hd] at h0
    exact psi_zero_le (x := x) h2 hb2 hb4 hb6 (by rw [← h0]; ring)

/- English proof (translation)
Take `⟨h1, h2a, h3, h4, h6, -⟩` from `hW`. Take `⟨hb2, hb4, hb6, hb8⟩` from `b_int W h1 h2a h3 h4 h6`. Consider the cases of `P with`. Consider the case `zero`. Express the relevant statement in the definitionally equal form `4 ≤ ‖(0 : K)‖ at hx`.

Rewrite `hx` using `[norm_zero]`. Evaluate the numerical expressions using `at hx`. Consider the case `some x y h`. Establish `hy : y ≠ W.toAffine.negY x y` using `fun e => hP ((add_self_iff h).2 (negY_iff.1 e))`. Rewrite using `[px_add_self h hy]`.

Conclude with `dup_core h2 hb2 hb4 hb6 hb8 hx (dup h.1 hy)`.
-/
lemma dup_big (hW : IntCurve W) (h2 : ‖(2 : K)‖ = 2⁻¹) (P : W.toAffine.Point)
    (hx : 4 ≤ ‖px W P‖) (hP : P + P ≠ 0) : 4 < ‖px W (P + P)‖ := by
  obtain ⟨h1, h2a, h3, h4, h6, -⟩ := hW
  obtain ⟨hb2, hb4, hb6, hb8⟩ := b_int W h1 h2a h3 h4 h6
  cases P with
  | zero =>
    change 4 ≤ ‖(0 : K)‖ at hx
    rw [norm_zero] at hx
    norm_num at hx
  | some x y h =>
    have hy : y ≠ W.toAffine.negY x y := fun e => hP ((add_self_iff h).2 (negY_iff.1 e))
    rw [px_add_self h hy]
    exact dup_core h2 hb2 hb4 hb6 hb8 hx (dup h.1 hy)

/- English proof (translation)
Assume the negation of the conclusion as `hge`. Use `push_neg at hge`. Establish `claim : ∀ j : ℕ, 4 < ‖px W ((2 ^ (j + 1)) • P)‖`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero`. Rewrite using `[zero_add, pow_one, two_nsmul]`. Conclude with `dup_big hW h2 P hge hP`. Consider the case `succ j ih`. Establish `hQ : (2 ^ (j + 1)) • P + (2 ^ (j + 1)) • P ≠ 0`.

Introduce `e`. Use `two_tors_le hW h2 _ e` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : (2 ^ (j + 1 + 1)) • P = (2 ^ (j + 1)) • P + (2 ^ (j + 1)) • P`. Rewrite using `[← add_nsmul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `dup_big hW h2 _ ih.le hQ`. Consider the cases of `k with`.

Consider the case `zero`. Rewrite `hk` using `[pow_zero, one_nsmul]`. Rewrite `hP` using `[hk, add_zero]`. Conclude with `hP rfl`. Consider the case `succ k`.

Establish `hc` using `claim k`. Rewrite `hc` using `[hk]`. Express the relevant statement in the definitionally equal form `4 < ‖(0 : K)‖ at hc`. Rewrite `hc` using `[norm_zero]`. Evaluate the numerical expressions using `at hc`.
-/
lemma tors_bound (hW : IntCurve W) (h2 : ‖(2 : K)‖ = 2⁻¹) (P : W.toAffine.Point) (k : ℕ)
    (hk : (2 ^ k) • P = 0) (hP : P + P ≠ 0) : ‖px W P‖ < 4 := by
  by_contra hge
  push_neg at hge
  have claim : ∀ j : ℕ, 4 < ‖px W ((2 ^ (j + 1)) • P)‖ := by
    intro j
    induction j with
    | zero =>
      rw [zero_add, pow_one, two_nsmul]
      exact dup_big hW h2 P hge hP
    | succ j ih =>
      have hQ : (2 ^ (j + 1)) • P + (2 ^ (j + 1)) • P ≠ 0 := by
        intro e
        have := two_tors_le hW h2 _ e
        linarith
      have e : (2 ^ (j + 1 + 1)) • P = (2 ^ (j + 1)) • P + (2 ^ (j + 1)) • P := by
        rw [← add_nsmul]
        congr 1
        ring
      rw [e]
      exact dup_big hW h2 _ ih.le hQ
  cases k with
  | zero =>
    rw [pow_zero, one_nsmul] at hk
    rw [hk, add_zero] at hP
    exact hP rfl
  | succ k =>
    have hc := claim k
    rw [hk] at hc
    change 4 < ‖(0 : K)‖ at hc
    rw [norm_zero] at hc
    norm_num at hc

/- English proof (translation)
Take `⟨h1, h2a, h3, h4, h6, -⟩` from `hW`. Take `⟨-, hb4, hb6, -⟩` from `b_int W h1 h2a h3 h4 h6`. Establish `hb2 : ‖W.b₂‖ = 1`. Simplify using `only [WeierstrassCurve.b₂]`. Rewrite using `[ndom (by rw [norm_pow, ha, one_pow, norm_mul, n4 h2]; nlinarith [norm_nonneg W.a₂]), norm_pow, ha, one_pow]`.

Consider the cases of `P with`. Consider the case `zero => exact (hP0 rfl).elim`. Consider the case `some x y h`. Establish `hd` using `(add_self_iff h).1 hP`. Establish `h0 : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0`.

Establish `e` using `psi_eq h.1`. Rewrite `e` using `[hd]`. Rewrite using `[← e]`. Expand and normalize the polynomial expressions, which then agree. Establish `hx4 : ‖x‖ = 4` using `psi_zero_eq (x := x) h2 hb2 hb4 hb6 hPE h0`.

Use `⟨hx4, fun hQ0 hQ hQE => ?_⟩` and prove the remaining obligations. Consider the cases of `Q with`. Consider the case `zero => exact (hQ0 rfl).elim`. Consider the case `some x' y' h'`. Establish `hd'` using `(add_self_iff h').1 hQ`.

Establish `h0' : 4 * x' ^ 3 + W.b₂ * x' ^ 2 + 2 * W.b₄ * x' + W.b₆ = 0`. Establish `e` using `psi_eq h'.1`. Rewrite `e` using `[hd']`. Rewrite using `[← e]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hx4' : ‖x'‖ = 4` using `psi_zero_eq (x := x') h2 hb2 hb4 hb6 hQE h0'`. Establish `hxx` using `psi_zero_unique h2 hb2.le hb4 hb6 hx4 hx4' h0 h0'`. Substitute `hxx` using the available equality. Establish `hyy : y = y'`. Establish `e2 : (2 : K) * y = 2 * y'` using `by linear_combination hd - hd'`.

Conclude with `mul_left_cancel₀ (two_ne h2) e2`. Substitute `hyy` using the available equality. Both sides reduce to the same expression.
-/
lemma two_torsion_kernel_norm_unique (hW : IntCurve W) (h2 : ‖(2 : K)‖ = 2⁻¹) (ha : ‖W.a₁‖ = 1)
    (P Q : W.toAffine.Point) (hP0 : P ≠ 0) (hP : P + P = 0) (hPE : InFormalGroupPoints P) :
    ‖px W P‖ = 4 ∧ (Q ≠ 0 → Q + Q = 0 → InFormalGroupPoints Q → P = Q) := by
  obtain ⟨h1, h2a, h3, h4, h6, -⟩ := hW
  obtain ⟨-, hb4, hb6, -⟩ := b_int W h1 h2a h3 h4 h6
  have hb2 : ‖W.b₂‖ = 1 := by
    simp only [WeierstrassCurve.b₂]
    rw [ndom (by rw [norm_pow, ha, one_pow, norm_mul, n4 h2]; nlinarith [norm_nonneg W.a₂]),
      norm_pow, ha, one_pow]
  cases P with
  | zero => exact (hP0 rfl).elim
  | some x y h =>
    have hd := (add_self_iff h).1 hP
    have h0 : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
      have e := psi_eq h.1
      rw [hd] at e
      rw [← e]
      ring
    have hx4 : ‖x‖ = 4 := psi_zero_eq (x := x) h2 hb2 hb4 hb6 hPE h0
    refine ⟨hx4, fun hQ0 hQ hQE => ?_⟩
    cases Q with
    | zero => exact (hQ0 rfl).elim
    | some x' y' h' =>
      have hd' := (add_self_iff h').1 hQ
      have h0' : 4 * x' ^ 3 + W.b₂ * x' ^ 2 + 2 * W.b₄ * x' + W.b₆ = 0 := by
        have e := psi_eq h'.1
        rw [hd'] at e
        rw [← e]
        ring
      have hx4' : ‖x'‖ = 4 := psi_zero_eq (x := x') h2 hb2 hb4 hb6 hQE h0'
      have hxx := psi_zero_unique h2 hb2.le hb4 hb6 hx4 hx4' h0 h0'
      subst hxx
      have hyy : y = y' := by
        have e2 : (2 : K) * y = 2 * y' := by linear_combination hd - hd'
        exact mul_left_cancel₀ (two_ne h2) e2
      subst hyy
      rfl

end Main

open Classical in
/- English proof (translation)
Introduce `K _ _ W hW h2 ha P Q hP0 hP hPE`. Conclude with `two_torsion_kernel_norm_unique hW h2 ha P Q hP0 hP hPE`.
-/
theorem two_torsion_kernel_unique_holds : TwoTorsionKernelUnique := by
  intro K _ _ W hW h2 ha P Q hP0 hP hPE
  exact two_torsion_kernel_norm_unique hW h2 ha P Q hP0 hP hPE

open Classical in
/- English proof (translation)
Introduce `K _ _ W hW h2 P k hk hP`. Conclude with `tors_bound hW h2 P k hk hP`.
-/
theorem torsion_norm_bound_holds : TorsBound := by
  intro K _ _ W hW h2 P k hk hP
  exact tors_bound hW h2 P k hk hP

/- English proof (translation)
Introduce `K _ _ _ W hM h2 x`. Take `⟨h1, h2a, h3, h4, h6⟩` from `hM`. Take `⟨hb2, hb4, -, -⟩` from `b_int W h1 h2a h3 h4 h6`. Establish `e : 3 * (x + W.b₂ / 12) ^ 2 - Formalism.L2.Th1.A.g₂ W / 4 = 3 * x ^ 2 + 2⁻¹ * W.b₂ * x + 2⁻¹ * W.b₄`. Simplify using `only [Formalism.L2.Th1.A.g₂, WeierstrassCurve.c₄]`.

Expand and normalize the polynomial expressions, which then agree. Establish `ni : ‖(2 : K)⁻¹‖ = 2` using `by rw [norm_inv, h2, inv_inv]`. Establish `t1 : ‖3 * x ^ 2‖ = ‖x‖ ^ 2` using `by rw [norm_mul, n3 h2, one_mul, norm_pow]`. Establish `t2 : ‖2⁻¹ * W.b₂ * x‖ ≤ 2 * ‖x‖`. Rewrite using `[norm_mul, norm_mul, ni]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hb2 (norm_nonneg x), norm_nonneg W.b₂]`. Establish `t3 : ‖2⁻¹ * W.b₄‖ ≤ 2`. Rewrite using `[norm_mul, ni]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[e]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hr : ‖2⁻¹ * W.b₂ * x + 2⁻¹ * W.b₄‖ < ‖3 * x ^ 2‖`. Rewrite using `[t1, hx]`. Conclude with `nadd_lt (t2.trans_lt (by rw [hx]; norm_num)) (t3.trans_lt (by norm_num))`.

Rewrite using `[add_assoc, ndom hr, t1, hx]`. Evaluate the numerical expressions. Introduce `hx`. Establish `r0` using `norm_nonneg x`. Conclude with `nadd_lt (nadd_lt (by rw [t1]; nlinarith) (t2.trans_lt (by linarith))) (t3.trans_lt (by norm_num))`.
-/
theorem kappa_norm_holds : KapNorm := by
  intro K _ _ _ W hM h2 x
  obtain ⟨h1, h2a, h3, h4, h6⟩ := hM
  obtain ⟨hb2, hb4, -, -⟩ := b_int W h1 h2a h3 h4 h6
  have e : 3 * (x + W.b₂ / 12) ^ 2 - Formalism.L2.Th1.A.g₂ W / 4
      = 3 * x ^ 2 + 2⁻¹ * W.b₂ * x + 2⁻¹ * W.b₄ := by
    simp only [Formalism.L2.Th1.A.g₂, WeierstrassCurve.c₄]
    ring
  have ni : ‖(2 : K)⁻¹‖ = 2 := by rw [norm_inv, h2, inv_inv]
  have t1 : ‖3 * x ^ 2‖ = ‖x‖ ^ 2 := by rw [norm_mul, n3 h2, one_mul, norm_pow]
  have t2 : ‖2⁻¹ * W.b₂ * x‖ ≤ 2 * ‖x‖ := by
    rw [norm_mul, norm_mul, ni]
    nlinarith [mul_le_mul_of_nonneg_right hb2 (norm_nonneg x), norm_nonneg W.b₂]
  have t3 : ‖2⁻¹ * W.b₄‖ ≤ 2 := by
    rw [norm_mul, ni]
    linarith
  rw [e]
  constructor
  · intro hx
    have hr : ‖2⁻¹ * W.b₂ * x + 2⁻¹ * W.b₄‖ < ‖3 * x ^ 2‖ := by
      rw [t1, hx]
      exact nadd_lt (t2.trans_lt (by rw [hx]; norm_num)) (t3.trans_lt (by norm_num))
    rw [add_assoc, ndom hr, t1, hx]
    norm_num
  · intro hx
    have r0 := norm_nonneg x
    exact nadd_lt (nadd_lt (by rw [t1]; nlinarith) (t2.trans_lt (by linarith))) (t3.trans_lt (by norm_num))

end Formalism.L2.Th1.B.KNorm
