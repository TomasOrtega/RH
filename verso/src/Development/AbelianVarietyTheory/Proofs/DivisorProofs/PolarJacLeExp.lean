import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.PolarJacBound

open MvPolynomial in
/- English proof (translation)
Unfold `_root_.Formalism.MainNotions.SchurIrreducible.shc`. Use `split_ifs with hx`. Evaluate the numerical expressions. Break down `lt_or_gt_of_ne hx with h | h` into its components or cases. Conclude with `(div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr h) h).le`.

Conclude with `(div_pos (Real.sinh_pos_iff.mpr h) h).le`.
-/
private lemma shc_nonneg' (x : ℝ) : 0 ≤ _root_.Formalism.MainNotions.SchurIrreducible.shc x := by
  unfold _root_.Formalism.MainNotions.SchurIrreducible.shc
  split_ifs with hx
  · norm_num
  · rcases lt_or_gt_of_ne hx with h | h
    · exact (div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr h) h).le
    · exact (div_pos (Real.sinh_pos_iff.mpr h) h).le

open MvPolynomial in
/- English proof (translation)
Rewrite using `[div_le_iff₀ hy, Real.sinh_eq]`. Establish `h1 : -(2 * y) + 1 ≤ Real.exp (-(2 * y))` using `Real.add_one_le_exp _`. Establish `h2 : Real.exp (-y) = Real.exp y * Real.exp (-(2 * y))`. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form.

Establish `h3 : 0 < Real.exp y` using `Real.exp_pos y`. Rewrite using `[h2]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h1 h3.le]`.
-/
private lemma sinh_div_le_exp_of_pos {y : ℝ} (hy : 0 < y) : Real.sinh y / y ≤ Real.exp y := by
  rw [div_le_iff₀ hy, Real.sinh_eq]
  have h1 : -(2 * y) + 1 ≤ Real.exp (-(2 * y)) := Real.add_one_le_exp _
  have h2 : Real.exp (-y) = Real.exp y * Real.exp (-(2 * y)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : 0 < Real.exp y := Real.exp_pos y
  rw [h2]
  nlinarith [mul_le_mul_of_nonneg_left h1 h3.le]

open MvPolynomial in
/- English proof (translation)
Unfold `_root_.Formalism.MainNotions.SchurIrreducible.shc`. Use `split_ifs with hx`. Simplify using `[hx]`. Break down `lt_or_gt_of_ne hx with h | h` into its components or cases. Rewrite using `[abs_of_neg h]`.

Use `sinh_div_le_exp_of_pos (neg_pos.mpr h)` as an intermediate fact. Rewrite `this` using `[Real.sinh_neg, neg_div_neg_eq]`. Then use the resulting hypothesis. Rewrite using `[abs_of_pos h]`. Conclude with `sinh_div_le_exp_of_pos h`.
-/
private lemma shc_le_exp_abs (x : ℝ) : _root_.Formalism.MainNotions.SchurIrreducible.shc x ≤ Real.exp |x| := by
  unfold _root_.Formalism.MainNotions.SchurIrreducible.shc
  split_ifs with hx
  · simp [hx]
  · rcases lt_or_gt_of_ne hx with h | h
    · rw [abs_of_neg h]
      have := sinh_div_le_exp_of_pos (neg_pos.mpr h)
      rwa [Real.sinh_neg, neg_div_neg_eq] at this
    · rw [abs_of_pos h]
      exact sinh_div_le_exp_of_pos h

open MvPolynomial in
/- English proof (translation)
Establish `e : ∀ i j, (if i < j then 4 * (a i + a j) else 0) = 4 * ((if i < j then a i else 0) + (if i < j then a j else 0))`. Apply the tactic sequence `intro i j; split_ifs <;> ring`. Repeatedly rewrite using `[e, ← Finset.mul_sum, Finset.sum_add_distrib]`. Rewrite using `[Finset.sum_comm (f := fun i j => if i < j then a j else 0), ← Finset.sum_add_distrib]`. Use `congr 1`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Establish `t : ∀ j, ((if i < j then a i else 0) + (if j < i then a i else 0)) = a i - (if i = j then a i else 0)`. Introduce `j`.

Break down `lt_trichotomy i j with hij | hij | hij` into its components or cases. Simplify using `[hij, hij.ne, not_lt.mpr hij.le]`. Simplify using `[hij]`. Simplify using `[hij, hij.ne', not_lt.mpr hij.le]`. Repeatedly rewrite using `[t, Finset.sum_sub_distrib, Finset.sum_ite_eq, hi, Finset.sum_const, Finset.card_range]`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma sum_sum_ite_lt_four_mul_add_eq (m : ℕ) (a : ℕ → ℝ) :
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, (if i < j then 4 * (a i + a j) else 0) =
      4 * (((m : ℝ) - 1) * ∑ i ∈ Finset.range m, a i) := by
  have e : ∀ i j, (if i < j then 4 * (a i + a j) else 0) =
      4 * ((if i < j then a i else 0) + (if i < j then a j else 0)) := by
    intro i j; split_ifs <;> ring
  simp_rw [e, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if i < j then a j else 0), ← Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.sum_add_distrib]
  have t : ∀ j, ((if i < j then a i else 0) + (if j < i then a i else 0)) =
      a i - (if i = j then a i else 0) := by
    intro j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, hij.ne, not_lt.mpr hij.le]
    · simp [hij]
    · simp [hij, hij.ne', not_lt.mpr hij.le]
  simp_rw [t, Finset.sum_sub_distrib, Finset.sum_ite_eq, hi, Finset.sum_const, Finset.card_range]
  simp; ring

open MvPolynomial in
/- English proof (translation)
Establish `hrow : ∀ a : Fin p, ∑ b : Fin q, ‖if (a : ℕ) = b then ((h a : ℝ) : ℂ) else 0‖ ^ 2 = if (a : ℕ) < q then h a ^ 2 else 0`. Introduce `a`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun j => ‖if (a : ℕ) = j then ((h a : ℝ) : ℂ) else 0‖ ^ 2) q]`. Establish `: ∀ j, ‖if (a : ℕ) = j then ((h a : ℝ) : ℂ) else 0‖ ^ 2 = if (a : ℕ) = j then h a ^ 2 else 0`. Apply the tactic sequence `intro j; split_ifs <;> simp`.

Repeatedly rewrite using `[this, Finset.sum_ite_eq, Finset.mem_range]`. Repeatedly rewrite using `[hrow]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => if i < q then h i ^ 2 else 0) p, ← Finset.sum_filter]`. Use `congr 1`. Use extensionality with `i`.

Simplify using `[lt_min_iff]`.
-/
private lemma sum_norm_sq_diag_eq_sum_range_min (p q : ℕ) (h : ℕ → ℝ) :
    ∑ a : Fin p, ∑ b : Fin q, ‖if (a : ℕ) = b then ((h a : ℝ) : ℂ) else 0‖ ^ 2 =
      ∑ i ∈ Finset.range (min p q), h i ^ 2 := by
  have hrow : ∀ a : Fin p, ∑ b : Fin q, ‖if (a : ℕ) = b then ((h a : ℝ) : ℂ) else 0‖ ^ 2 =
      if (a : ℕ) < q then h a ^ 2 else 0 := by
    intro a
    rw [Fin.sum_univ_eq_sum_range (fun j => ‖if (a : ℕ) = j then ((h a : ℝ) : ℂ) else 0‖ ^ 2) q]
    have : ∀ j, ‖if (a : ℕ) = j then ((h a : ℝ) : ℂ) else 0‖ ^ 2 =
        if (a : ℕ) = j then h a ^ 2 else 0 := by
      intro j; split_ifs <;> simp
    simp_rw [this, Finset.sum_ite_eq, Finset.mem_range]
  simp_rw [hrow]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < q then h i ^ 2 else 0) p, ← Finset.sum_filter]
  congr 1
  ext i; simp [lt_min_iff]

open MvPolynomial in
/- English proof (translation)
Simplify using `only [_root_.Formalism.BasicNotions.TH.hsNorm, _root_.Formalism.MainNotions.SchurIrreducible.aOf, _root_.Formalism.MainNotions.SchurIrreducible.pOf]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_comm (s := (Finset.univ : Finset (Fin q))), sum_norm_sq_diag_eq_sum_range_min, ← two_mul, Real.sqrt_mul (by norm_num)]`.
-/
private lemma hsNorm_aOf_eq_sqrt_two_mul_sum_sq (p q : ℕ) (h : ℕ → ℝ) :
    _root_.Formalism.BasicNotions.TH.hsNorm (_root_.Formalism.MainNotions.SchurIrreducible.aOf p q h) = Real.sqrt (2 * ∑ i ∈ Finset.range (min p q), h i ^ 2) := by
  simp only [_root_.Formalism.BasicNotions.TH.hsNorm, _root_.Formalism.MainNotions.SchurIrreducible.aOf, _root_.Formalism.MainNotions.SchurIrreducible.pOf]
  simp
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin q))), sum_norm_sq_diag_eq_sum_range_min, ← two_mul,
    Real.sqrt_mul (by norm_num)]

open MvPolynomial in

/- English proof (translation)
Introduce `p q h`. Use `set r := Finset.range (min p q) with hr`. Use `set k := max p q - min p q with hk`. Establish `hA : ∏ i ∈ r, _root_.Formalism.MainNotions.SchurIrreducible.shc (2 * h i) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i) ^ (2 * k) ≤ ∏ i ∈ r, Real.exp ((2 + 2 * (k : ℝ)) * |h i|)`. Use `Finset.prod_le_prod (fun i _ => mul_nonneg (shc_nonneg' _) (pow_nonneg (shc_nonneg' _) _)) fun i _ => ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.exp_nat_mul, ← Real.exp_add, abs_mul, abs_two]`. Use `push_cast`. Put the polynomial expressions in normal form. Establish `hB : (∏ i ∈ r, ∏ j ∈ r, if i < j then (_root_.Formalism.MainNotions.SchurIrreducible.shc (h i - h j) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i + h j)) ^ 2 else 1) ≤ ∏ i ∈ r, ∏ j ∈ r, Real.exp (if i < j then 4 * (|h i| + |h j|) else 0)`.

Use `Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => ?_) fun i _ => Finset.prod_le_prod (fun j _ => ?_) fun j _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `sq_nonneg _`. Conclude with `zero_le_one`. Use `split_ifs`.

Conclude with `sq_nonneg _`. Conclude with `zero_le_one`. Use `split_ifs`. Establish `h1 : _root_.Formalism.MainNotions.SchurIrreducible.shc (h i - h j) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i + h j) ≤ Real.exp (2 * (|h i| + |h j|))`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear relations using `[abs_sub (h i) (h j), abs_add_le (h i) (h j)]`. Combine the equalities or inequalities in the displayed calculation. Simplify using the standard rewrite rules. Use `set S := ∑ i ∈ r, |h i| with hS`. Use `set Q := ∑ i ∈ r, h i ^ 2 with hQ`.

Establish `hS0 : 0 ≤ S` using `Finset.sum_nonneg fun i _ => abs_nonneg _`. Establish `hCS : S ^ 2 ≤ (min p q : ℕ) * Q`. Use `Finset.sum_mul_sq_le_sq_mul_sq r (fun _ => (1 : ℝ)) (fun i => |h i|)` as an intermediate fact. Simplify `this` using `[hr, sq_abs]`. Establish `hkey : 2 * S ≤ Real.sqrt (2 * (min p q : ℕ)) * Real.sqrt (2 * Q)`.

Rewrite using `[← Real.sqrt_mul (by positivity)]`. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `hn : ((p + q : ℕ) : ℝ) = (max p q : ℕ) + (min p q : ℕ)`. Rewrite using `[← Nat.cast_add, max_add_min]`.

Establish `hkR : (k : ℝ) = (max p q : ℕ) - (min p q : ℕ)`. Rewrite using `[hk, Nat.cast_sub min_le_max]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `sq_nonneg _`. Conclude with `zero_le_one) (Finset.prod_nonneg fun i _ => (Real.exp_pos _).le)`.

Use `_ = Real.exp ((2 + 2 * (k : ℝ)) * S + 4 * (((min p q : ℕ) : ℝ) - 1) * S) := by`. Repeatedly rewrite using `[← Real.exp_sum]`. Rewrite using `[← Real.exp_add]`. Use `congr 1`. Rewrite using `[hS, hr, sum_sum_ite_lt_four_mul_add_eq, ← Finset.mul_sum]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := by`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Rewrite using `[hsNorm_aOf_eq_sqrt_two_mul_sum_sq, mul_assoc, hn]`. Establish `hm0 : (0 : ℝ) ≤ (min p q : ℕ)` using `Nat.cast_nonneg _`.

Establish `hM0 : (0 : ℝ) ≤ (max p q : ℕ)` using `Nat.cast_nonneg _`. Rewrite using `[hkR]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hkey (add_nonneg hM0 hm0)]`.
-/
theorem _root_.GlobalTheory.PolarJacBound.polarJac_le_exp : ∀ (p q : ℕ) (h : ℕ → ℝ), (∏ i ∈ Finset.range (min p q), _root_.Formalism.MainNotions.SchurIrreducible.shc (2 * h i) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i) ^ (2 * (max p q - min p q))) * (∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q), if i < j then (_root_.Formalism.MainNotions.SchurIrreducible.shc (h i - h j) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i + h j)) ^ 2 else 1) ≤ Real.exp (((p + q : ℕ) : ℝ) * Real.sqrt (2 * (min p q : ℕ)) * _root_.Formalism.BasicNotions.TH.hsNorm (_root_.Formalism.MainNotions.SchurIrreducible.aOf p q h)) := by
  intro p q h
  set r := Finset.range (min p q) with hr
  set k := max p q - min p q with hk
  have hA : ∏ i ∈ r, _root_.Formalism.MainNotions.SchurIrreducible.shc (2 * h i) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i) ^ (2 * k) ≤
      ∏ i ∈ r, Real.exp ((2 + 2 * (k : ℝ)) * |h i|) := by
    refine Finset.prod_le_prod
      (fun i _ => mul_nonneg (shc_nonneg' _) (pow_nonneg (shc_nonneg' _) _)) fun i _ => ?_
    calc _root_.Formalism.MainNotions.SchurIrreducible.shc (2 * h i) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i) ^ (2 * k)
        ≤ Real.exp |2 * h i| * Real.exp |h i| ^ (2 * k) :=
          mul_le_mul (shc_le_exp_abs _)
            (pow_le_pow_left₀ (shc_nonneg' _) (shc_le_exp_abs _) _)
            (pow_nonneg (shc_nonneg' _) _) (Real.exp_pos _).le
      _ = Real.exp ((2 + 2 * (k : ℝ)) * |h i|) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, abs_mul, abs_two]; push_cast; ring_nf
  have hB : (∏ i ∈ r, ∏ j ∈ r,
        if i < j then (_root_.Formalism.MainNotions.SchurIrreducible.shc (h i - h j) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i + h j)) ^ 2 else 1) ≤
      ∏ i ∈ r, ∏ j ∈ r, Real.exp (if i < j then 4 * (|h i| + |h j|) else 0) := by
    refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => ?_) fun i _ =>
      Finset.prod_le_prod (fun j _ => ?_) fun j _ => ?_
    · split_ifs
      · exact sq_nonneg _
      · exact zero_le_one
    · split_ifs
      · exact sq_nonneg _
      · exact zero_le_one
    · split_ifs
      · have h1 : _root_.Formalism.MainNotions.SchurIrreducible.shc (h i - h j) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i + h j) ≤
            Real.exp (2 * (|h i| + |h j|)) := by
          calc _root_.Formalism.MainNotions.SchurIrreducible.shc (h i - h j) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i + h j)
              ≤ Real.exp |h i - h j| * Real.exp |h i + h j| :=
                mul_le_mul (shc_le_exp_abs _) (shc_le_exp_abs _) (shc_nonneg' _)
                  (Real.exp_pos _).le
            _ = Real.exp (|h i - h j| + |h i + h j|) := (Real.exp_add _ _).symm
            _ ≤ Real.exp (2 * (|h i| + |h j|)) := by
                gcongr
                linarith [abs_sub (h i) (h j), abs_add_le (h i) (h j)]
        calc (_root_.Formalism.MainNotions.SchurIrreducible.shc (h i - h j) * _root_.Formalism.MainNotions.SchurIrreducible.shc (h i + h j)) ^ 2
            ≤ Real.exp (2 * (|h i| + |h j|)) ^ 2 :=
              pow_le_pow_left₀ (mul_nonneg (shc_nonneg' _) (shc_nonneg' _)) h1 2
          _ = Real.exp (4 * (|h i| + |h j|)) := by rw [← Real.exp_nat_mul]; ring_nf
      · simp
  set S := ∑ i ∈ r, |h i| with hS
  set Q := ∑ i ∈ r, h i ^ 2 with hQ
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hCS : S ^ 2 ≤ (min p q : ℕ) * Q := by
    have := Finset.sum_mul_sq_le_sq_mul_sq r (fun _ => (1 : ℝ)) (fun i => |h i|)
    simpa [hr, sq_abs] using this
  have hkey : 2 * S ≤ Real.sqrt (2 * (min p q : ℕ)) * Real.sqrt (2 * Q) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hn : ((p + q : ℕ) : ℝ) = (max p q : ℕ) + (min p q : ℕ) := by
    rw [← Nat.cast_add, max_add_min]
  have hkR : (k : ℝ) = (max p q : ℕ) - (min p q : ℕ) := by
    rw [hk, Nat.cast_sub min_le_max]
  calc _ ≤ (∏ i ∈ r, Real.exp ((2 + 2 * (k : ℝ)) * |h i|)) *
        ∏ i ∈ r, ∏ j ∈ r, Real.exp (if i < j then 4 * (|h i| + |h j|) else 0) :=
        mul_le_mul hA hB (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => by
          split_ifs
          · exact sq_nonneg _
          · exact zero_le_one) (Finset.prod_nonneg fun i _ => (Real.exp_pos _).le)
    _ = Real.exp ((2 + 2 * (k : ℝ)) * S + 4 * (((min p q : ℕ) : ℝ) - 1) * S) := by
        simp_rw [← Real.exp_sum]
        rw [← Real.exp_add]
        congr 1
        rw [hS, hr, sum_sum_ite_lt_four_mul_add_eq, ← Finset.mul_sum]
        ring
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [hsNorm_aOf_eq_sqrt_two_mul_sum_sq, mul_assoc, hn]
        have hm0 : (0 : ℝ) ≤ (min p q : ℕ) := Nat.cast_nonneg _
        have hM0 : (0 : ℝ) ≤ (max p q : ℕ) := Nat.cast_nonneg _
        rw [hkR]
        nlinarith [mul_le_mul_of_nonneg_left hkey (add_nonneg hM0 hm0)]

end GlobalTheory.PolarJacBound
