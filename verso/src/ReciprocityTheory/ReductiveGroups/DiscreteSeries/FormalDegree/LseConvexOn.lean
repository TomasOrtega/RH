import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.EigenvectorUnitaryMulStar

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

section LSE

variable {ι : Type*} [Fintype ι]

/- English proof (translation)
Establish `hex : ∃ i, 0 < w i`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h0 : ∑ i, w i = 0` using `Finset.sum_eq_zero (fun i _ => le_antisymm (h i) (hw0 i))`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨i, hi⟩` from `hex`. Conclude with `Finset.sum_pos' (fun j _ => mul_nonneg (hw0 j) (Real.exp_pos _).le) ⟨i, Finset.mem_univ _, mul_pos hi (Real.exp_pos _)⟩`.
-/
theorem lse_pos (w y : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (t : ℝ) :
    0 < ∑ i, w i * Real.exp (t * y i) := by
  have hex : ∃ i, 0 < w i := by
    by_contra h
    push_neg at h
    have h0 : ∑ i, w i = 0 := Finset.sum_eq_zero (fun i _ => le_antisymm (h i) (hw0 i))
    linarith
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw0 j) (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ _, mul_pos hi (Real.exp_pos _)⟩

/- English proof (translation)
Use `⟨convex_univ, fun t1 _ t2 _ a b ha hb hab => ?_⟩` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Use `set A := ∑ i, w i * Real.exp (t1 * y i) with hA`. Use `set B := ∑ i, w i * Real.exp (t2 * y i) with hB`. Establish `hA0 : 0 < A` using `lse_pos w y hw0 hw1 t1`.

Establish `hB0 : 0 < B` using `lse_pos w y hw0 hw1 t2`. Use `set E := Real.exp (a * Real.log A + b * Real.log B) with hE`. Establish `key : ∀ i, Real.exp ((a * t1 + b * t2) * y i) ≤ (a * (Real.exp (t1 * y i) / A) + b * (Real.exp (t2 * y i) / B)) * E`. Introduce `i`. Establish `h1` using `convexOn_exp.2 (Set.mem_univ (t1 * y i - Real.log A)) (Set.mem_univ (t2 * y i - Real.log B)) ha hb hab`.

Simplify using `only [smul_eq_mul] at h1`. Establish `e1 : Real.exp (t1 * y i - Real.log A) = Real.exp (t1 * y i) / A`. Rewrite using `[Real.exp_sub, Real.exp_log hA0]`. Establish `e2 : Real.exp (t2 * y i - Real.log B) = Real.exp (t2 * y i) / B`. Rewrite using `[Real.exp_sub, Real.exp_log hB0]`.

Rewrite `h1` using `[e1, e2]`. Establish `e3 : Real.exp ((a * t1 + b * t2) * y i) = Real.exp (a * (t1 * y i - Real.log A) + b * (t2 * y i - Real.log B)) * E`. Rewrite using `[hE, ← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e3]`. Conclude with `mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le`. Establish `hsum : ∑ i, w i * Real.exp ((a * t1 + b * t2) * y i) ≤ E`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hA, hB, Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]`.

Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = E := by rw [div_self hA0.ne', div_self hB0.ne', mul_one, mul_one, hab, one_mul]`. Establish `hpos` using `lse_pos w y hw0 hw1 (a * t1 + b * t2)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lse_convexOn (w y : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    ConvexOn ℝ Set.univ (fun t : ℝ => Real.log (∑ i, w i * Real.exp (t * y i))) := by
  refine ⟨convex_univ, fun t1 _ t2 _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set A := ∑ i, w i * Real.exp (t1 * y i) with hA
  set B := ∑ i, w i * Real.exp (t2 * y i) with hB
  have hA0 : 0 < A := lse_pos w y hw0 hw1 t1
  have hB0 : 0 < B := lse_pos w y hw0 hw1 t2
  set E := Real.exp (a * Real.log A + b * Real.log B) with hE
  have key : ∀ i, Real.exp ((a * t1 + b * t2) * y i) ≤
      (a * (Real.exp (t1 * y i) / A) + b * (Real.exp (t2 * y i) / B)) * E := by
    intro i
    have h1 := convexOn_exp.2 (Set.mem_univ (t1 * y i - Real.log A))
      (Set.mem_univ (t2 * y i - Real.log B)) ha hb hab
    simp only [smul_eq_mul] at h1
    have e1 : Real.exp (t1 * y i - Real.log A) = Real.exp (t1 * y i) / A := by
      rw [Real.exp_sub, Real.exp_log hA0]
    have e2 : Real.exp (t2 * y i - Real.log B) = Real.exp (t2 * y i) / B := by
      rw [Real.exp_sub, Real.exp_log hB0]
    rw [e1, e2] at h1
    have e3 : Real.exp ((a * t1 + b * t2) * y i) =
        Real.exp (a * (t1 * y i - Real.log A) + b * (t2 * y i - Real.log B)) * E := by
      rw [hE, ← Real.exp_add]; congr 1; ring
    rw [e3]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hsum : ∑ i, w i * Real.exp ((a * t1 + b * t2) * y i) ≤ E := by
    calc ∑ i, w i * Real.exp ((a * t1 + b * t2) * y i)
        ≤ ∑ i, w i * ((a * (Real.exp (t1 * y i) / A) + b * (Real.exp (t2 * y i) / B)) * E) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (key i) (hw0 i))
      _ = (a * (A / A) + b * (B / B)) * E := by
          rw [hA, hB, Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
      _ = E := by rw [div_self hA0.ne', div_self hB0.ne', mul_one, mul_one, hab, one_mul]
  have hpos := lse_pos w y hw0 hw1 (a * t1 + b * t2)
  calc Real.log (∑ i, w i * Real.exp ((a * t1 + b * t2) * y i)) ≤ Real.log E :=
        Real.log_le_log hpos hsum
    _ = a * Real.log A + b * Real.log B := Real.log_exp _

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_add, mul_one, Finset.sum_add_distrib, hw1, hw2, add_zero]`. Use `_ ≤ ∑ i, w i * Real.exp (y i) := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (y i)]) (hw0 i))`.
-/
theorem lse_one_le (w y : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hw2 : ∑ i, w i * y i = 0) : 1 ≤ ∑ i, w i * Real.exp (y i) := by
  calc (1 : ℝ) = ∑ i, w i * (1 + y i) := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib, hw1, hw2, add_zero]
    _ ≤ ∑ i, w i * Real.exp (y i) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
          (by linarith [Real.add_one_le_exp (y i)]) (hw0 i))

/- English proof (translation)
Establish `hpos : 0 < ∑ i, w i * Real.exp (y i)` using `by simpa using lse_pos w y hw0 hw1 1`. Establish `hle : ∑ i, w i * Real.exp (y i) ≤ 1 + ∑ i, w i * y i ^ 2`. Combine the equalities or inequalities in the displayed calculation. Establish `h` using `abs_le.mp (Real.abs_exp_sub_one_sub_id_le (hy i))`. Combine the linear relations using `[h.2]) (hw0 i))`.

Use `_ = 1 + ∑ i, w i * y i ^ 2 := by`. Simplify using `only [mul_add, mul_one, Finset.sum_add_distrib, hw1, hw2, add_zero]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lse_upper (w y : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hw2 : ∑ i, w i * y i = 0) (hy : ∀ i, |y i| ≤ 1) :
    Real.log (∑ i, w i * Real.exp (y i)) ≤ ∑ i, w i * y i ^ 2 := by
  have hpos : 0 < ∑ i, w i * Real.exp (y i) := by simpa using lse_pos w y hw0 hw1 1
  have hle : ∑ i, w i * Real.exp (y i) ≤ 1 + ∑ i, w i * y i ^ 2 := by
    calc ∑ i, w i * Real.exp (y i) ≤ ∑ i, w i * (1 + y i + y i ^ 2) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
            (by
              have h := abs_le.mp (Real.abs_exp_sub_one_sub_id_le (hy i))
              linarith [h.2]) (hw0 i))
      _ = 1 + ∑ i, w i * y i ^ 2 := by
          simp only [mul_add, mul_one, Finset.sum_add_distrib, hw1, hw2, add_zero]
  calc Real.log (∑ i, w i * Real.exp (y i)) ≤ Real.log (1 + ∑ i, w i * y i ^ 2) :=
        Real.log_le_log hpos hle
    _ ≤ (1 + ∑ i, w i * y i ^ 2) - 1 := Real.log_le_sub_one_of_pos (by linarith)
    _ = ∑ i, w i * y i ^ 2 := by ring

/- English proof (translation)
Use `set V := ∑ i, w i * y i ^ 2 with hV`. Establish `hD : 1 ≤ ∑ i, w i * Real.exp (y i)` using `lse_one_le w y hw0 hw1 hw2`. Establish `hV0 : 0 ≤ V` using `Finset.sum_nonneg (fun i _ => mul_nonneg (hw0 i) (sq_nonneg _))`. Establish `hVle : V ≤ ep ^ 2 / 4`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_ (hw0 i))` and prove the remaining obligations. Use `sq_abs (y i)` as an intermediate fact. Establish `h1` using `hy i`. Establish `h2` using `abs_nonneg (y i)`. Use the polynomial consequences of the given equalities and inequalities.

Use `_ = ep ^ 2 / 4 := by rw [← Finset.sum_mul, hw1]; ring`. Establish `hterm : ∀ i, 1 + y i + y i ^ 2 * (1 / 2 - ep / 9) ≤ Real.exp (y i)`. Introduce `i`. Establish `hyi : |y i| ≤ 1` using `(hy i).trans (by linarith)`. Establish `hb` using `Real.exp_bound hyi (n := 3) (by norm_num)`.

Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb`. Evaluate the numerical expressions using `at hb`. Establish `hb'` using `(abs_le.1 hb).1`. Establish `hc : |y i| ^ 3 ≤ ep / 2 * y i ^ 2`. Establish `: |y i| ^ 3 = |y i| * y i ^ 2` using `by rw [pow_succ, sq_abs]; ring`.

Rewrite using `[this]`. Conclude with `mul_le_mul_of_nonneg_right (hy i) (sq_nonneg _)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hlow : 1 + V * (1 / 2 - ep / 9) ≤ ∑ i, w i * Real.exp (y i)`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [mul_add, mul_one, Finset.sum_add_distrib, hw1, hw2, add_zero, hV, Finset.sum_mul]`. Use `congrArg _ (Finset.sum_congr rfl (fun i _ => by ring))` and prove the remaining obligations. Use `_ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hterm i) (hw0 i))`. Use `set c := V / 2 * (1 - ep) with hc`. Establish `hc0 : 0 ≤ c` using `mul_nonneg (by linarith) (by linarith)`.

Establish `hc1 : c ≤ V / 2` using `by nlinarith`. Establish `hcabs : |c| ≤ 1` using `by rw [abs_of_nonneg hc0]; nlinarith`. Establish `hexp : Real.exp c ≤ 1 + c + c ^ 2`. Use `(abs_le.1 (Real.abs_exp_sub_one_sub_id_le hcabs)).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hcc : c ^ 2 ≤ V * ep ^ 2 / 8` using `by nlinarith`. Establish `hfin : 1 + c + c ^ 2 ≤ ∑ i, w i * Real.exp (y i)`. Establish `: c + c ^ 2 ≤ V * (1 / 2 - ep / 9)`. Rewrite using `[hc]`. Establish `: V * ep ^ 2 / 8 ≤ V * ep * (7 / 18)` using `by nlinarith`.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpos : 0 < ∑ i, w i * Real.exp (y i)` using `by linarith`. Rewrite using `[← Real.exp_le_exp, Real.exp_log hpos]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lse_lower (w y : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hw2 : ∑ i, w i * y i = 0) {ep : ℝ} (he0 : 0 ≤ ep) (he1 : ep ≤ 1)
    (hy : ∀ i, |y i| ≤ ep / 2) :
    (∑ i, w i * y i ^ 2) / 2 * (1 - ep) ≤ Real.log (∑ i, w i * Real.exp (y i)) := by
  set V := ∑ i, w i * y i ^ 2 with hV
  have hD : 1 ≤ ∑ i, w i * Real.exp (y i) := lse_one_le w y hw0 hw1 hw2
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun i _ => mul_nonneg (hw0 i) (sq_nonneg _))
  have hVle : V ≤ ep ^ 2 / 4 := by
    calc V ≤ ∑ i, w i * (ep / 2) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_ (hw0 i))
          have := sq_abs (y i)
          have h1 := hy i
          have h2 := abs_nonneg (y i)
          nlinarith
      _ = ep ^ 2 / 4 := by rw [← Finset.sum_mul, hw1]; ring

  have hterm : ∀ i, 1 + y i + y i ^ 2 * (1 / 2 - ep / 9) ≤ Real.exp (y i) := by
    intro i
    have hyi : |y i| ≤ 1 := (hy i).trans (by linarith)
    have hb := Real.exp_bound hyi (n := 3) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
    norm_num at hb
    have hb' := (abs_le.1 hb).1
    have hc : |y i| ^ 3 ≤ ep / 2 * y i ^ 2 := by
      have : |y i| ^ 3 = |y i| * y i ^ 2 := by rw [pow_succ, sq_abs]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (hy i) (sq_nonneg _)
    nlinarith
  have hlow : 1 + V * (1 / 2 - ep / 9) ≤ ∑ i, w i * Real.exp (y i) := by
    calc 1 + V * (1 / 2 - ep / 9) = ∑ i, w i * (1 + y i + y i ^ 2 * (1 / 2 - ep / 9)) := by
          simp only [mul_add, mul_one, Finset.sum_add_distrib, hw1, hw2, add_zero, hV,
            Finset.sum_mul]
          refine congrArg _ (Finset.sum_congr rfl (fun i _ => by ring))
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hterm i) (hw0 i))
  set c := V / 2 * (1 - ep) with hc
  have hc0 : 0 ≤ c := mul_nonneg (by linarith) (by linarith)
  have hc1 : c ≤ V / 2 := by nlinarith
  have hcabs : |c| ≤ 1 := by rw [abs_of_nonneg hc0]; nlinarith
  have hexp : Real.exp c ≤ 1 + c + c ^ 2 := by
    have := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le hcabs)).2
    linarith
  have hcc : c ^ 2 ≤ V * ep ^ 2 / 8 := by nlinarith
  have hfin : 1 + c + c ^ 2 ≤ ∑ i, w i * Real.exp (y i) := by
    have : c + c ^ 2 ≤ V * (1 / 2 - ep / 9) := by
      rw [hc]
      have : V * ep ^ 2 / 8 ≤ V * ep * (7 / 18) := by nlinarith
      nlinarith
    linarith
  have hpos : 0 < ∑ i, w i * Real.exp (y i) := by linarith
  rw [← Real.exp_le_exp, Real.exp_log hpos]
  linarith

end LSE

end ReciprocityTheory.ChartRestriction.DS
