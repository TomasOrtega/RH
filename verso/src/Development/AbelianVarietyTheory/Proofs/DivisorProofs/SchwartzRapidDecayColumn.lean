import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL

noncomputable section

open Classical MeasureTheory NumberField

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

/- English proof (translation)
Introduce `E _ _ _ a r f`. Use `haveI : (volume : Measure (Fin a → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Establish `hc : Continuous fun x : Fin a → Cinf E => toL (colU r x).val`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous fun x : Fin a → Cinf E => (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j + (if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0)`.

Use `split_ifs`. Conclude with `continuous_const.add (continuous_apply i)`. Conclude with `continuous_const.add continuous_const`. Establish `hci : Continuous fun x : Fin a → Cinf E => toL ((colU r x)⁻¹).val`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Continuous fun x : Fin a → Cinf E => (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j - (if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0)`. Use `split_ifs`. Conclude with `continuous_const.sub (continuous_apply i)`. Conclude with `continuous_const.sub continuous_const`. Use `set c₁ : ℝ := ‖(1 : Cinf E)‖`.

Establish `hent : ∀ (s : Cinf E) (x : Fin a → Cinf E), ‖s‖ ≤ 1 → ‖toL ((1 : Matrix (Fin a) (Fin a) (Cinf E)) + Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then s * x i else 0))‖ ≤ c₁ + ‖x‖`. Introduce `s x hs`. Use `pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun i => pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖(1 : Matrix (Fin a) (Fin a) (Cinf E)) i j + (if (j : ℕ) = r ∧ (i : ℕ) < r then s * x i else 0)‖ ≤ _`. Use `(norm_add_le _ _).trans (add_le_add ?_ ?_)` and prove the remaining obligations.

Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `le_rfl`. Simplify using `[c₁]`. Use `split_ifs`.

Conclude with `(norm_mul_le _ _).trans ((mul_le_mul hs (norm_le_pi_norm x i) (norm_nonneg _) zero_le_one).trans (by simp))`. Simplify using the standard rewrite rules. Establish `hH : ∀ x : Fin a → Cinf E, height (colU r x) ≤ (1 + 2 * c₁) + 2 * ‖x‖`. Introduce `x`. Establish `e1 : (colU r x).val = (1 : Matrix (Fin a) (Fin a) (Cinf E)) + Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then (1 : Cinf E) * x i else 0)`.

Simplify using `[colU]`. Establish `e2 : ((colU r x)⁻¹).val = (1 : Matrix (Fin a) (Fin a) (Cinf E)) + Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then (-1 : Cinf E) * x i else 0)`. Express the relevant statement in the definitionally equal form `1 - _ = _`. Rewrite using `[sub_eq_add_neg]`. Use `congr 1`.

Use extensionality with `i j w`. Simplify using `only [Matrix.neg_apply, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `n1 : ‖(-1 : Cinf E)‖ ≤ 1`. Rewrite using `[norm_neg]; exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => by simp`.

Establish `n0 : ‖(1 : Cinf E)‖ ≤ 1` using `(pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => by simp`. Unfold `height`. Rewrite using `[e1, e2]`. Combine the linear relations using `[hent 1 x n0, hent (-1) x n1]`. Use `⟨f.continuous.measurable, ?_, fun N => ?_⟩` and prove the remaining obligations.

Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Conclude with `((continuous_apply j).comp ((continuous_apply i).comp hc)).measurable`. Use `set A : ℝ := 1 + 2 * c₁`. Establish `hA : 0 ≤ A` using `by positivity`. Establish `hdom : Integrable fun x : Fin a → Cinf E => (A + 2 * ‖x‖) ^ N * ‖f x‖`.

Establish `e : (fun x : Fin a → Cinf E => (A + 2 * ‖x‖) ^ N * ‖f x‖) = fun x => ∑ m ∈ Finset.range (N + 1), (2 ^ m * A ^ (N - m) * (N.choose m : ℝ)) * (‖x‖ ^ m * ‖f x‖)`. Use function extensionality and compare the values at `x`. Rewrite using `[add_comm, add_pow, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[mul_pow]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `integrable_finset_sum _ fun m _ => (f.integrable_pow_mul volume m).const_mul _`. Establish `hht : Continuous fun x : Fin a → Cinf E => height (colU r x)`. Unfold `height`.

Conclude with `(continuous_const.add hc.norm).add hci.norm`. Use `Integrable.mono' hdom ((f.continuous.norm.mul (hht.pow N)).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Establish `h1 : 1 ≤ height (colU r x)` using `one_le_height _`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]`. Conclude with `mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (hH x) N) (norm_nonneg _)`.
-/
theorem isRapidInf_colU : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (r : ℕ)
    (f : SchwartzMap (Fin a → GlobalTheory.CuspRep.Cinf E) ℂ),
    GlobalTheory.JSW.IsRapidInf (volume : Measure (Fin a → GlobalTheory.CuspRep.Cinf E)) (fun x => f x) (GlobalTheory.JSW.colU r) := by
  intro E _ _ _ a r f
  haveI : (volume : Measure (Fin a → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hc : Continuous fun x : Fin a → Cinf E => toL (colU r x).val := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun x : Fin a → Cinf E =>
      (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j + (if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0)
    split_ifs
    · exact continuous_const.add (continuous_apply i)
    · exact continuous_const.add continuous_const
  have hci : Continuous fun x : Fin a → Cinf E => toL ((colU r x)⁻¹).val := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun x : Fin a → Cinf E =>
      (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j - (if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0)
    split_ifs
    · exact continuous_const.sub (continuous_apply i)
    · exact continuous_const.sub continuous_const
  set c₁ : ℝ := ‖(1 : Cinf E)‖
  have hent : ∀ (s : Cinf E) (x : Fin a → Cinf E), ‖s‖ ≤ 1 →
      ‖toL ((1 : Matrix (Fin a) (Fin a) (Cinf E)) + Matrix.of
        (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then s * x i else 0))‖ ≤ c₁ + ‖x‖ := by
    intro s x hs
    refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun i => pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun j => ?_
    change ‖(1 : Matrix (Fin a) (Fin a) (Cinf E)) i j + (if (j : ℕ) = r ∧ (i : ℕ) < r then s * x i else 0)‖ ≤ _
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Matrix.one_apply]; split_ifs
      · exact le_rfl
      · simp [c₁]
    · split_ifs
      · exact (norm_mul_le _ _).trans ((mul_le_mul hs (norm_le_pi_norm x i) (norm_nonneg _) zero_le_one).trans (by simp))
      · simp
  have hH : ∀ x : Fin a → Cinf E, height (colU r x) ≤ (1 + 2 * c₁) + 2 * ‖x‖ := by
    intro x
    have e1 : (colU r x).val = (1 : Matrix (Fin a) (Fin a) (Cinf E)) + Matrix.of
        (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then (1 : Cinf E) * x i else 0) := by
      simp [colU]
    have e2 : ((colU r x)⁻¹).val = (1 : Matrix (Fin a) (Fin a) (Cinf E)) + Matrix.of
        (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then (-1 : Cinf E) * x i else 0) := by
      change 1 - _ = _
      rw [sub_eq_add_neg]
      congr 1
      ext i j w
      simp only [Matrix.neg_apply, Matrix.of_apply]
      split_ifs <;> simp
    have n1 : ‖(-1 : Cinf E)‖ ≤ 1 := by
      rw [norm_neg]; exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => by simp
    have n0 : ‖(1 : Cinf E)‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => by simp
    unfold height
    rw [e1, e2]
    linarith [hent 1 x n0, hent (-1) x n1]
  refine ⟨f.continuous.measurable, ?_, fun N => ?_⟩
  · refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    exact ((continuous_apply j).comp ((continuous_apply i).comp hc)).measurable
  · set A : ℝ := 1 + 2 * c₁
    have hA : 0 ≤ A := by positivity
    have hdom : Integrable fun x : Fin a → Cinf E => (A + 2 * ‖x‖) ^ N * ‖f x‖ := by
      have e : (fun x : Fin a → Cinf E => (A + 2 * ‖x‖) ^ N * ‖f x‖) = fun x =>
          ∑ m ∈ Finset.range (N + 1), (2 ^ m * A ^ (N - m) * (N.choose m : ℝ)) * (‖x‖ ^ m * ‖f x‖) := by
        funext x
        rw [add_comm, add_pow, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [mul_pow]; ring
      rw [e]
      exact integrable_finset_sum _ fun m _ => (f.integrable_pow_mul volume m).const_mul _
    have hht : Continuous fun x : Fin a → Cinf E => height (colU r x) := by
      unfold height
      exact (continuous_const.add hc.norm).add hci.norm
    refine Integrable.mono' hdom ((f.continuous.norm.mul (hht.pow N)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 : 1 ≤ height (colU r x) := one_le_height _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (hH x) N) (norm_nonneg _)

end GlobalTheory.JSW
