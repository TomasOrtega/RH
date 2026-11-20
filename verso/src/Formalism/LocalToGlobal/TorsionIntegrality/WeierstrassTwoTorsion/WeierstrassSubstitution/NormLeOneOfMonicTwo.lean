import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementQ
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowDouble

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

namespace Q2

section Parity

variable {R : Type u} [CommRing R]

/- English proof (translation)
Rewrite using `[PowerSeries.rescale_eq_subst, neg_one_smul]`.
-/
theorem subst_neg_X (f : R⟦X⟧) : f.subst (-X : R⟦X⟧) = rescale (-1) f := by
  rw [PowerSeries.rescale_eq_subst, neg_one_smul]

/- English proof (translation)
Rewrite using `[subst_neg_X, PowerSeries.coeff_rescale]`.
-/
theorem coeff_subst_neg_X (f : R⟦X⟧) (n : ℕ) :
    coeff n (f.subst (-X : R⟦X⟧)) = (-1) ^ n * coeff n f := by
  rw [subst_neg_X, PowerSeries.coeff_rescale]

variable {K : Type u} [Field K] [CharZero K]

/- English proof (translation)
Establish `h1` using `coeff_subst_neg_X f n`. Rewrite `h1` using `[h, hn.neg_one_pow]`. Establish `h2 : (2 : K) * coeff n f = 0` using `by linear_combination h1`. Simplify using `using h2`.
-/
theorem coeff_odd_eq_zero {f : K⟦X⟧} (h : f.subst (-X : K⟦X⟧) = f) {n : ℕ} (hn : Odd n) :
    coeff n f = 0 := by
  have h1 := coeff_subst_neg_X f n
  rw [h, hn.neg_one_pow] at h1
  have h2 : (2 : K) * coeff n f = 0 := by linear_combination h1
  simpa using h2

end Parity

section Ball

variable {K : Type} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
The claim follows from `(IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)`.
-/
theorem nadd {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

/- English proof (translation)
Rewrite using `[norm_neg]`. Conclude with `ha`.
-/
theorem nneg {a : K} (ha : ‖a‖ ≤ 1) : ‖-a‖ ≤ 1 := by
  rw [norm_neg]
  exact ha

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `nadd ha (nneg hb)`.
-/
theorem nsub {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact nadd ha (nneg hb)

/- English proof (translation)
Rewrite using `[norm_mul]`. Use polynomial arithmetic with `[norm_nonneg a, norm_nonneg b]`.
-/
theorem nmul {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  nlinarith [norm_nonneg a, norm_nonneg b]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ]`. Conclude with `nmul ih ha`.
-/
theorem npow {a : K} (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a ^ n‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact nmul ih ha

/- English proof (translation)
Establish `h1 : ‖(1 : K)‖ ≤ 1` using `by simp`. Establish `h` using `nadd h1 h1`. Rewrite `h` using `[one_add_one_eq_two]`. Then use the resulting hypothesis.
-/
theorem ntwo : ‖(2 : K)‖ ≤ 1 := by
  have h1 : ‖(1 : K)‖ ≤ 1 := by simp
  have h := nadd h1 h1
  rwa [one_add_one_eq_two] at h

/- English proof (translation)
Establish `h1 : ‖(1 : K)‖ ≤ 1` using `by simp`. Establish `h : (3 : K) = 2 + 1` using `by norm_num`. Rewrite using `[h]`. Conclude with `nadd ntwo h1`.
-/
theorem nthree : ‖(3 : K)‖ ≤ 1 := by
  have h1 : ‖(1 : K)‖ ≤ 1 := by simp
  have h : (3 : K) = 2 + 1 := by norm_num
  rw [h]
  exact nadd ntwo h1

/- English proof (translation)
Assume the negation of the conclusion as `hy`. Use `push_neg at hy`. Establish `h2 : y ^ 2 = c + -(b * y)` using `by rw [← h]; ring`. Establish `h3 : ‖y ^ 2‖ ≤ max ‖c‖ ‖-(b * y)‖`. Rewrite using `[h2]`.

Conclude with `IsUltrametricDist.norm_add_le_max _ _`. Rewrite `h3` using `[norm_neg, norm_pow, norm_mul]`. Establish `hby : ‖b‖ * ‖y‖ ≤ ‖y‖` using `by nlinarith [norm_nonneg b, norm_nonneg y]`. Establish `hmax : max ‖c‖ (‖b‖ * ‖y‖) ≤ ‖y‖` using `max_le (by linarith) hby`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_le_one_of_monic_two {y b c : K} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (h : y ^ 2 + b * y = c) : ‖y‖ ≤ 1 := by
  by_contra hy
  push_neg at hy
  have h2 : y ^ 2 = c + -(b * y) := by rw [← h]; ring
  have h3 : ‖y ^ 2‖ ≤ max ‖c‖ ‖-(b * y)‖ := by
    rw [h2]
    exact IsUltrametricDist.norm_add_le_max _ _
  rw [norm_neg, norm_pow, norm_mul] at h3
  have hby : ‖b‖ * ‖y‖ ≤ ‖y‖ := by nlinarith [norm_nonneg b, norm_nonneg y]
  have hmax : max ‖c‖ (‖b‖ * ‖y‖) ≤ ‖y‖ := max_le (by linarith) hby
  nlinarith

end Ball

end Q2

open Q2

/- English proof (translation)
Introduce `K _ _ _ W xT yT hE h2`. Take `⟨hroot, -, hkap, -, -, -, heven, -⟩` from `twoTorsionZ K W xT yT hE h2`. Use `⟨hroot, fun n hn => coeff_odd_eq_zero heven hn, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨h1, h2', h3, h4, h6⟩ hx`. Establish `hy : ‖yT‖ ≤ 1`.

Rewrite `hE` using `[WeierstrassCurve.Affine.equation_iff]`. Use `norm_le_one_of_monic_two (b := W.a₁ * xT + W.a₃) (c := xT ^ 3 + W.a₂ * xT ^ 2 + W.a₄ * xT + W.a₆) (nadd (nmul h1 hx) h3) (nadd (nadd (nadd (npow hx 3) (nmul h2' (npow hx 2))) (nmul h4 hx)) h6) ?_` and prove the remaining obligations. Take the linear combination `hE`. Use `⟨hy, ?_, ?_⟩` and prove the remaining obligations. Establish `: W.b₂ / 12 - (xT + W.b₂ / 12) = -xT` using `by ring`.

Rewrite using `[this]`. Conclude with `nneg hx`. Rewrite using `[hkap]`. Conclude with `nsub (nadd (nadd (nmul nthree (npow hx 2)) (nmul (nmul ntwo h2') hx)) h4) (nmul h1 hy)`.
-/
theorem two_curves_relation : BridgeTwoMore := by
  intro K _ _ _ W xT yT hE h2
  obtain ⟨hroot, -, hkap, -, -, -, heven, -⟩ := twoTorsionZ K W xT yT hE h2
  refine ⟨hroot, fun n hn => coeff_odd_eq_zero heven hn, ?_⟩
  rintro ⟨h1, h2', h3, h4, h6⟩ hx
  have hy : ‖yT‖ ≤ 1 := by
    rw [WeierstrassCurve.Affine.equation_iff] at hE
    refine norm_le_one_of_monic_two (b := W.a₁ * xT + W.a₃)
      (c := xT ^ 3 + W.a₂ * xT ^ 2 + W.a₄ * xT + W.a₆) (nadd (nmul h1 hx) h3)
      (nadd (nadd (nadd (npow hx 3) (nmul h2' (npow hx 2))) (nmul h4 hx)) h6) ?_
    linear_combination hE
  refine ⟨hy, ?_, ?_⟩
  · have : W.b₂ / 12 - (xT + W.b₂ / 12) = -xT := by ring
    rw [this]; exact nneg hx
  · rw [hkap]
    exact nsub (nadd (nadd (nmul nthree (npow hx 2)) (nmul (nmul ntwo h2') hx)) h4) (nmul h1 hy)

/- English proof (translation)
Introduce `K _ _ W x y x' y' hF hF' hx0 hy0`. Take `⟨-, hx, hy⟩` from `hF`. Take `⟨-, hx', hy'⟩` from `hF'`. Establish `hR : ∀ (n : ℕ) (r : K), n ≠ 0 → (n : K) * r = 0 → r = 0` using `fun n r hn h => (mul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 hn)`. Simplify using `only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄] at hx hy hx' hy'`.

Establish `dx : derivative K (x - x') = 2 * (y - y') + C W.a₁ * (x - x')`. Rewrite using `[map_sub, hx, hx']`. Expand and normalize the polynomial expressions, which then agree. Establish `dy : derivative K (y - y') = (x - x') * (3 * (x + x') + 2 * C W.a₂) - C W.a₁ * (y - y')`. Rewrite using `[map_sub, hy, hy']`.

Expand and normalize the polynomial expressions, which then agree. Establish `cx : constantCoeff (x - x') = 0` using `by rw [map_sub, hx0, sub_self]`. Establish `cy : constantCoeff (y - y') = 0` using `by rw [map_sub, hy0, sub_self]`. Establish `key : ∀ n : ℕ, X ^ n ∣ x - x' ∧ X ^ n ∣ y - y'`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Take `⟨ix, iy⟩` from `ih`. Use `⟨Nn.X_pow_succ_dvd_of_derivative hR cx ?_, Nn.X_pow_succ_dvd_of_derivative hR cy ?_⟩` and prove the remaining obligations.

Rewrite using `[dx]`. Conclude with `dvd_add (Dvd.dvd.mul_left iy _) (Dvd.dvd.mul_left ix _)`. Rewrite using `[dy]`. Conclude with `dvd_sub (Dvd.dvd.mul_right ix _) (Dvd.dvd.mul_left iy _)`. Conclude with `⟨sub_eq_zero.1 (Nn.eq_zero_of_forall_X_pow_dvd fun n => (key n).1), sub_eq_zero.1 (Nn.eq_zero_of_forall_X_pow_dvd fun n => (key n).2)⟩`.
-/
theorem flow_unique_integral : FlowUniqueZ.{u} := by
  intro K _ _ W x y x' y' hF hF' hx0 hy0
  obtain ⟨-, hx, hy⟩ := hF
  obtain ⟨-, hx', hy'⟩ := hF'
  have hR : ∀ (n : ℕ) (r : K), n ≠ 0 → (n : K) * r = 0 → r = 0 := fun n r hn h =>
    (mul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 hn)
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄] at hx hy hx' hy'
  have dx : derivative K (x - x') = 2 * (y - y') + C W.a₁ * (x - x') := by
    rw [map_sub, hx, hx']; ring
  have dy : derivative K (y - y')
      = (x - x') * (3 * (x + x') + 2 * C W.a₂) - C W.a₁ * (y - y') := by
    rw [map_sub, hy, hy']; ring
  have cx : constantCoeff (x - x') = 0 := by rw [map_sub, hx0, sub_self]
  have cy : constantCoeff (y - y') = 0 := by rw [map_sub, hy0, sub_self]
  have key : ∀ n : ℕ, X ^ n ∣ x - x' ∧ X ^ n ∣ y - y' := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨ix, iy⟩ := ih
      refine ⟨Nn.X_pow_succ_dvd_of_derivative hR cx ?_, Nn.X_pow_succ_dvd_of_derivative hR cy ?_⟩
      · rw [dx]
        exact dvd_add (Dvd.dvd.mul_left iy _) (Dvd.dvd.mul_left ix _)
      · rw [dy]
        exact dvd_sub (Dvd.dvd.mul_right ix _) (Dvd.dvd.mul_left iy _)
  exact ⟨sub_eq_zero.1 (Nn.eq_zero_of_forall_X_pow_dvd fun n => (key n).1),
    sub_eq_zero.1 (Nn.eq_zero_of_forall_X_pow_dvd fun n => (key n).2)⟩

end Formalism.L2.Th1.A
