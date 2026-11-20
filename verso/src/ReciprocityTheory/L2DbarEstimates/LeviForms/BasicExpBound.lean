import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

/- English proof (translation)
Establish `hx0 : (0 : ℝ) ≤ x` using `by linarith`. Establish `h4` using `Real.sum_le_exp_of_nonneg hx0 4`. Simplify using `[Finset.sum_range_succ, Nat.factorial] at h4`. Establish `hl` using `Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < x)`. Use polynomial arithmetic with `[sq_nonneg (x - 7 / 5), mul_nonneg hx0 (sq_nonneg (x - 7 / 5)), mul_nonneg (by linarith : (0:ℝ) ≤ x - 1) (sq_nonneg (x - 7 / 5))]`.
-/
theorem basic_exp_bound (x : ℝ) (hx : 1 ≤ x) :
    (x + 1) ^ 2 + (x + Real.log x) ≤ 2 * Real.exp x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have h4 := Real.sum_le_exp_of_nonneg hx0 4
  simp [Finset.sum_range_succ, Nat.factorial] at h4
  have hl := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < x)
  nlinarith [sq_nonneg (x - 7 / 5), mul_nonneg hx0 (sq_nonneg (x - 7 / 5)),
    mul_nonneg (by linarith : (0:ℝ) ≤ x - 1) (sq_nonneg (x - 7 / 5))]

/- English proof (translation)
Establish `h` using `Real.exp_one_lt_d9`. Establish `h0 : 0 ≤ Real.exp 1` using `(Real.exp_pos 1).le`. Establish `: Real.exp 7 = Real.exp 1 ^ 7`. Rewrite using `[← Real.exp_nat_mul]`. Evaluate the numerical expressions.

Rewrite using `[this]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem basic_exp_seven : Real.exp 7 ≤ 1250 := by
  have h := Real.exp_one_lt_d9
  have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have : Real.exp 7 = Real.exp 1 ^ 7 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 7 ≤ (2.7182818286 : ℝ) ^ 7 := by gcongr
    _ ≤ 1250 := by norm_num

/- English proof (translation)
Introduce `X`. Establish `he2 : 0 < ε ^ 2` using `by positivity`. Establish `hQ : 0 < A + ε ^ 2` using `by linarith`. Establish `hlog : Real.log (A + ε ^ 2) ≤ Real.log (1 + ε ^ 2)` using `Real.log_le_log hQ (by linarith)`. Establish `hX : 1 ≤ X` using `by simp only [X]; linarith`.

Establish `hX0 : 0 < X` using `by linarith`. Establish `hlX : 0 ≤ Real.log X` using `Real.log_nonneg hX`. Establish `hlX'` using `Real.log_le_sub_one_of_pos hX0`. Use `⟨hX, by linarith, ?_, by nlinarith, ?_, ?_⟩` and prove the remaining obligations. Establish `: 1 / X ≤ 1` using `by rw [div_le_one hX0]; exact hX`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `: Real.log (ε ^ 2) ≤ Real.log (A + ε ^ 2)` using `Real.log_le_log he2 (by linarith)`. Simplify using `only [X]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : (1 : ℝ) - X = Real.log (A + ε ^ 2) - Real.log (1 + ε ^ 2)` using `by simp only [X]; ring`.

Rewrite using `[h1, Real.exp_sub, Real.exp_log hQ, Real.exp_log (by positivity)]`. Clear the denominators using the available nonvanishing facts.
-/
theorem basic_real (A ε : ℝ) (hε : 0 < ε) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) :
    let X := 1 + Real.log (1 + ε ^ 2) - Real.log (A + ε ^ 2)
    1 ≤ X ∧ 1 ≤ X + Real.log X ∧ 1 + 1 / X ≤ 2 ∧ X + Real.log X ≤ (X + 1) ^ 2 ∧
      X ≤ 1 + Real.log (1 + ε ^ 2) - Real.log (ε ^ 2) ∧
      A + ε ^ 2 = (1 + ε ^ 2) * Real.exp (1 - X) := by
  intro X
  have he2 : 0 < ε ^ 2 := by positivity
  have hQ : 0 < A + ε ^ 2 := by linarith
  have hlog : Real.log (A + ε ^ 2) ≤ Real.log (1 + ε ^ 2) :=
    Real.log_le_log hQ (by linarith)
  have hX : 1 ≤ X := by simp only [X]; linarith
  have hX0 : 0 < X := by linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlX' := Real.log_le_sub_one_of_pos hX0
  refine ⟨hX, by linarith, ?_, by nlinarith, ?_, ?_⟩
  · have : 1 / X ≤ 1 := by rw [div_le_one hX0]; exact hX
    linarith
  · have : Real.log (ε ^ 2) ≤ Real.log (A + ε ^ 2) := Real.log_le_log he2 (by linarith)
    simp only [X]; linarith
  · have h1 : (1 : ℝ) - X = Real.log (A + ε ^ 2) - Real.log (1 + ε ^ 2) := by simp only [X]; ring
    rw [h1, Real.exp_sub, Real.exp_log hQ, Real.exp_log (by positivity)]
    field_simp

/- English proof (translation)
Introduce `g ph ph2 r j ε δ hr hε hA`. Establish `hev : ∀ x, 0 ≤ ev n g ph r x ∧ ev n g ph r x ≤ 1`. Introduce `x`. Establish `hr2 : 0 < r ^ 2` using `by positivity`. Use `⟨by unfold ev; positivity, ?_⟩` and prove the remaining obligations.

Unfold `ev`. Rewrite using `[div_le_one hr2]`. Conclude with `hA x`. Establish `hR : ∀ x, _` using `fun x => basic_real (ev n g ph r x) ε hε (hev x).1 (hev x).2`. Establish `hxx : ∀ x, xx n g ph r ε x = 1 + Real.log (1 + ε ^ 2) - Real.log (ev n g ph r x + ε ^ 2)` using `fun x => rfl`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Take `⟨h1, h2, h3, h4, -⟩` from `hR x`. Simplify using `only [eta, kap, hxx]`. Conclude with `⟨h1, h2, h3, h4⟩`.

Use `⟨Real.log (1 + Real.log (1 + ε ^ 2) - Real.log (ε ^ 2) + Real.log (1 + Real.log (1 + ε ^ 2) - Real.log (ε ^ 2))), fun x => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2, -, -, h5, -⟩` from `hR x`. Simplify using `only [twist, eta, hxx]`. Use `set X := 1 + Real.log (1 + ε ^ 2) - Real.log (ev n g ph r x + ε ^ 2)`. Use `set B := 1 + Real.log (1 + ε ^ 2) - Real.log (ε ^ 2)`.

Establish `hl0 : 0 ≤ Real.log (X + Real.log X)` using `Real.log_nonneg h2`. Establish `hlB : Real.log X ≤ Real.log B` using `Real.log_le_log (by linarith) h5`. Establish `: Real.log (X + Real.log X) ≤ Real.log (B + Real.log B)` using `Real.log_le_log (by linarith) (by linarith)`. Rewrite using `[abs_neg, abs_of_nonneg hl0]`. Conclude with `this`.

Introduce `h50 x hx`. Take `⟨h1, h2, -, -, -, -⟩` from `hR x`. Simplify using `only [eta, hxx]`. Use `set X := 1 + Real.log (1 + ε ^ 2) - Real.log (ev n g ph r x + ε ^ 2)`. Establish `hlX : 0 ≤ Real.log X` using `Real.log_nonneg h1`.

Establish `he2 : 0 < ε ^ 2` using `by positivity`. Establish `hQ : ev n g ph r x + ε ^ 2 ≤ 2 * ε ^ 2` using `by linarith`. Establish `hQ0 : 0 < ev n g ph r x + ε ^ 2` using `by linarith [(hev x).1]`. Establish `hsm : 2 * ε ^ 2 ≤ Real.exp (-7)`. Establish `hε2 : ε ^ 2 ≤ (1 / 50) ^ 2` using `by gcongr`.

Establish `: (1 : ℝ) / 1250 ≤ Real.exp (-7)`. Rewrite using `[Real.exp_neg, one_div]`. Conclude with `inv_anti₀ (Real.exp_pos 7) basic_exp_seven`. Use the polynomial consequences of the given equalities and inequalities. Establish `hlQ : Real.log (ev n g ph r x + ε ^ 2) ≤ -7`.

Rewrite using `[Real.log_le_iff_le_exp hQ0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl1 : 0 ≤ Real.log (1 + ε ^ 2)` using `Real.log_nonneg (by linarith)`. Simplify using `only [X] at hlX ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `hn hδ hδε x`. Take `⟨h1, -, -, -, -, h6⟩` from `hR x`. Establish `hD` using `basic_exp_bound _ h1`. Simplify using `only [eta, hxx, wgt, lw] at hD ⊢`. Use `set X := 1 + Real.log (1 + ε ^ 2) - Real.log (ev n g ph r x + ε ^ 2)`.

Use `set A := ev n g ph r x`. Use `set E := Real.exp (-ph2 x - ((n : ℝ) + j) * ph x)`. Use `set D := (X + 1) ^ 2 + (X + Real.log X)`. Establish `hA0 : 0 ≤ A` using `(hev x).1`. Establish `hAδ : 0 < A + δ ^ 2` using `by positivity`.

Establish `hD0 : 0 < D`. Establish `: 0 ≤ Real.log X` using `Real.log_nonneg h1`. Check the signs of the components of the expression. Establish `hE : 0 < E` using `Real.exp_pos _`. Establish `hexp : Real.exp (-(ph2 x + ((n : ℝ) + j) * ph x + n * Real.log (A + δ ^ 2))) = E / (A + δ ^ 2) ^ n`.

Rewrite using `[show -(ph2 x + ((n : ℝ) + j) * ph x + n * Real.log (A + δ ^ 2)) = (-ph2 x - ((n : ℝ) + j) * ph x) - n * Real.log (A + δ ^ 2) by ring, Real.exp_sub, ← Real.log_pow, Real.exp_log (by positivity)]`. Rewrite using `[hexp]`. Establish `hpow : (A + δ ^ 2) ^ n ≤ (1 + ε ^ 2) ^ n * Real.exp (1 - X)`. Establish `hle : A + δ ^ 2 ≤ (1 + ε ^ 2) * Real.exp (1 - X)`. Rewrite using `[← h6]; have : δ ^ 2 ≤ ε ^ 2 := by gcongr`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Conclude with `pow_le_of_le_one (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith)) (by omega)`. Establish `hkey : (A + δ ^ 2) ^ n * D ≤ 2 * Real.exp 1 * (1 + ε ^ 2) ^ n`. Establish `h2 : Real.exp (1 - X) * D ≤ 2 * Real.exp 1`.

Rewrite using `[Real.exp_sub]`. Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ (Real.exp_pos X)]`. Use polynomial arithmetic with `[Real.exp_pos 1]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_div, mul_div_assoc', le_div_iff₀ (by positivity)]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hkey hE.le]`.
-/
theorem basic (n : ℕ) (M : Type u) : BasicStatement n M := by
  intro g ph ph2 r j ε δ hr hε hA
  have hev : ∀ x, 0 ≤ ev n g ph r x ∧ ev n g ph r x ≤ 1 := by
    intro x
    have hr2 : 0 < r ^ 2 := by positivity
    refine ⟨by unfold ev; positivity, ?_⟩
    unfold ev
    rw [div_le_one hr2]; exact hA x
  have hR : ∀ x, _ := fun x => basic_real (ev n g ph r x) ε hε (hev x).1 (hev x).2
  have hxx : ∀ x, xx n g ph r ε x =
      1 + Real.log (1 + ε ^ 2) - Real.log (ev n g ph r x + ε ^ 2) := fun x => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨h1, h2, h3, h4, -⟩ := hR x
    simp only [eta, kap, hxx]
    exact ⟨h1, h2, h3, h4⟩
  · refine ⟨Real.log (1 + Real.log (1 + ε ^ 2) - Real.log (ε ^ 2) +
      Real.log (1 + Real.log (1 + ε ^ 2) - Real.log (ε ^ 2))), fun x => ?_⟩
    obtain ⟨h1, h2, -, -, h5, -⟩ := hR x
    simp only [twist, eta, hxx]
    set X := 1 + Real.log (1 + ε ^ 2) - Real.log (ev n g ph r x + ε ^ 2)
    set B := 1 + Real.log (1 + ε ^ 2) - Real.log (ε ^ 2)
    have hl0 : 0 ≤ Real.log (X + Real.log X) := Real.log_nonneg h2
    have hlB : Real.log X ≤ Real.log B := Real.log_le_log (by linarith) h5
    have : Real.log (X + Real.log X) ≤ Real.log (B + Real.log B) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [abs_neg, abs_of_nonneg hl0]; exact this
  · intro h50 x hx
    obtain ⟨h1, h2, -, -, -, -⟩ := hR x
    simp only [eta, hxx]
    set X := 1 + Real.log (1 + ε ^ 2) - Real.log (ev n g ph r x + ε ^ 2)
    have hlX : 0 ≤ Real.log X := Real.log_nonneg h1
    have he2 : 0 < ε ^ 2 := by positivity
    have hQ : ev n g ph r x + ε ^ 2 ≤ 2 * ε ^ 2 := by linarith
    have hQ0 : 0 < ev n g ph r x + ε ^ 2 := by linarith [(hev x).1]
    have hsm : 2 * ε ^ 2 ≤ Real.exp (-7) := by
      have hε2 : ε ^ 2 ≤ (1 / 50) ^ 2 := by gcongr
      have : (1 : ℝ) / 1250 ≤ Real.exp (-7) := by
        rw [Real.exp_neg, one_div]; exact inv_anti₀ (Real.exp_pos 7) basic_exp_seven
      nlinarith
    have hlQ : Real.log (ev n g ph r x + ε ^ 2) ≤ -7 := by
      rw [Real.log_le_iff_le_exp hQ0]; linarith
    have hl1 : 0 ≤ Real.log (1 + ε ^ 2) := Real.log_nonneg (by linarith)
    simp only [X] at hlX ⊢
    linarith
  · intro hn hδ hδε x
    obtain ⟨h1, -, -, -, -, h6⟩ := hR x
    have hD := basic_exp_bound _ h1
    simp only [eta, hxx, wgt, lw] at hD ⊢
    set X := 1 + Real.log (1 + ε ^ 2) - Real.log (ev n g ph r x + ε ^ 2)
    set A := ev n g ph r x
    set E := Real.exp (-ph2 x - ((n : ℝ) + j) * ph x)
    set D := (X + 1) ^ 2 + (X + Real.log X)
    have hA0 : 0 ≤ A := (hev x).1
    have hAδ : 0 < A + δ ^ 2 := by positivity
    have hD0 : 0 < D := by
      have : 0 ≤ Real.log X := Real.log_nonneg h1
      positivity
    have hE : 0 < E := Real.exp_pos _
    have hexp : Real.exp (-(ph2 x + ((n : ℝ) + j) * ph x + n * Real.log (A + δ ^ 2))) =
        E / (A + δ ^ 2) ^ n := by
      rw [show -(ph2 x + ((n : ℝ) + j) * ph x + n * Real.log (A + δ ^ 2)) =
        (-ph2 x - ((n : ℝ) + j) * ph x) - n * Real.log (A + δ ^ 2) by ring, Real.exp_sub,
        ← Real.log_pow, Real.exp_log (by positivity)]
    rw [hexp]

    have hpow : (A + δ ^ 2) ^ n ≤ (1 + ε ^ 2) ^ n * Real.exp (1 - X) := by
      have hle : A + δ ^ 2 ≤ (1 + ε ^ 2) * Real.exp (1 - X) := by
        rw [← h6]; have : δ ^ 2 ≤ ε ^ 2 := by gcongr
        linarith
      calc (A + δ ^ 2) ^ n ≤ ((1 + ε ^ 2) * Real.exp (1 - X)) ^ n := by gcongr
        _ = (1 + ε ^ 2) ^ n * Real.exp (1 - X) ^ n := by rw [mul_pow]
        _ ≤ (1 + ε ^ 2) ^ n * Real.exp (1 - X) := by
          gcongr
          exact pow_le_of_le_one (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))
            (by omega)
    have hkey : (A + δ ^ 2) ^ n * D ≤ 2 * Real.exp 1 * (1 + ε ^ 2) ^ n := by
      have h2 : Real.exp (1 - X) * D ≤ 2 * Real.exp 1 := by
        rw [Real.exp_sub]
        rw [div_mul_eq_mul_div, div_le_iff₀ (Real.exp_pos X)]
        nlinarith [Real.exp_pos 1]
      calc (A + δ ^ 2) ^ n * D ≤ (1 + ε ^ 2) ^ n * Real.exp (1 - X) * D := by gcongr
        _ = (1 + ε ^ 2) ^ n * (Real.exp (1 - X) * D) := by ring
        _ ≤ (1 + ε ^ 2) ^ n * (2 * Real.exp 1) := by gcongr
        _ = 2 * Real.exp 1 * (1 + ε ^ 2) ^ n := by ring
    rw [div_div, mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hkey hE.le]

end ReciprocityTheory.L2DbarEstimates.I
