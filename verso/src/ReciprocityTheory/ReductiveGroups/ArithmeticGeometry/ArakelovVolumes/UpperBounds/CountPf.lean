import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountRhoPArithStatement

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace CountPf

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `hTr : (0 : ℝ) < T` using `by exact_mod_cast hT`.

Establish `hA : ((T + (k + 1)).choose (k + 1) : ℝ) * (k + 1) = (T + k + 1) * ((T + k).choose k : ℝ)`. Establish `h` using `Nat.add_one_mul_choose_eq (T + k) k`. Rewrite using `[show T + (k + 1) = T + k + 1 by ring]`. Establish `h' : ((T + k + 1) * (T + k).choose k : ℕ) = ((T + k + 1).choose (k + 1) * (k + 1) : ℕ)` using `h`. Use `congrArg (fun t : ℕ => (t : ℝ)) h'` as an intermediate fact.

Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB : ((T + c + (k + 1)).choose (k + 1) : ℝ) * (k + 1) = (T + c + k + 1) * ((T + c + k).choose k : ℝ)`. Establish `h` using `Nat.add_one_mul_choose_eq (T + c + k) k`. Rewrite using `[show T + c + (k + 1) = T + c + k + 1 by ring]`.

Establish `h' : ((T + c + k + 1) * (T + c + k).choose k : ℕ) = ((T + c + k + 1).choose (k + 1) * (k + 1) : ℕ)` using `h`. Use `congrArg (fun t : ℕ => (t : ℝ)) h'` as an intermediate fact. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk1 : (0 : ℝ) < k + 1` using `by positivity`.

Establish `hBn : (0 : ℝ) ≤ ((T + c + k).choose k : ℝ)` using `Nat.cast_nonneg _`. Establish `hAn : (0 : ℝ) ≤ ((T + k).choose k : ℝ)` using `Nat.cast_nonneg _`. Establish `hc0 : (0 : ℝ) ≤ c` using `Nat.cast_nonneg _`. Use `push_cast`. Rewrite using `[← mul_le_mul_iff_of_pos_right hk1, mul_assoc, hB, hA]`.

Distinguish the cases in `hs : 1 - ((k : ℝ) + 1) * c / T ≤ 0`. Establish `: (1 - ((k : ℝ) + 1) * c / T) * ((T + c + k + 1) * ((T + c + k).choose k : ℝ)) ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg hs (by positivity)`. Establish `: (0 : ℝ) ≤ (T + k + 1) * ((T + k).choose k : ℝ)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `push_neg at hs set u := 1 - (k : ℝ) * c / T with hu`.

Establish `hu1 : u ≤ 1`. Establish `: 0 ≤ (k : ℝ) * c / T` using `by positivity`. Rewrite using `[hu]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcT : (c : ℝ) / T * T = c` using `by field_simp`.

Establish `e1 : 1 - ((k : ℝ) + 1) * c / T = u - c / T` using `by rw [hu]; ring`. Rewrite using `[e1]`. Establish `step : (u - c / T) * (T + c + k + 1) ≤ u * (T + k + 1)`. Establish `: (u - c / T) * (T + c + k + 1) = u * (T + k + 1) + (u * c - c / T * T - c / T * (c + k + 1))` using `by ring`. Rewrite using `[this, hcT]`.

Establish `h1 : u * c ≤ c` using `by nlinarith`. Establish `h2 : 0 ≤ (c : ℝ) / T * (c + k + 1)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hupos : 0 ≤ u - c / T` using `by linarith`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ratio (T c : ℕ) (hT : 0 < T) : ∀ k : ℕ,
    (1 - (k : ℝ) * c / T) * ((T + c + k).choose k : ℝ) ≤ ((T + k).choose k : ℝ) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hTr : (0 : ℝ) < T := by exact_mod_cast hT
    have hA : ((T + (k + 1)).choose (k + 1) : ℝ) * (k + 1) = (T + k + 1) * ((T + k).choose k : ℝ) := by
      have h := Nat.add_one_mul_choose_eq (T + k) k
      rw [show T + (k + 1) = T + k + 1 by ring]
      have h' : ((T + k + 1) * (T + k).choose k : ℕ) = ((T + k + 1).choose (k + 1) * (k + 1) : ℕ) := h
      have := congrArg (fun t : ℕ => (t : ℝ)) h'
      push_cast at this
      linarith
    have hB : ((T + c + (k + 1)).choose (k + 1) : ℝ) * (k + 1) = (T + c + k + 1) * ((T + c + k).choose k : ℝ) := by
      have h := Nat.add_one_mul_choose_eq (T + c + k) k
      rw [show T + c + (k + 1) = T + c + k + 1 by ring]
      have h' : ((T + c + k + 1) * (T + c + k).choose k : ℕ) = ((T + c + k + 1).choose (k + 1) * (k + 1) : ℕ) := h
      have := congrArg (fun t : ℕ => (t : ℝ)) h'
      push_cast at this
      linarith
    have hk1 : (0 : ℝ) < k + 1 := by positivity
    have hBn : (0 : ℝ) ≤ ((T + c + k).choose k : ℝ) := Nat.cast_nonneg _
    have hAn : (0 : ℝ) ≤ ((T + k).choose k : ℝ) := Nat.cast_nonneg _
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    push_cast
    rw [← mul_le_mul_iff_of_pos_right hk1, mul_assoc, hB, hA]
    by_cases hs : 1 - ((k : ℝ) + 1) * c / T ≤ 0
    · have : (1 - ((k : ℝ) + 1) * c / T) * ((T + c + k + 1) * ((T + c + k).choose k : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hs (by positivity)
      have : (0 : ℝ) ≤ (T + k + 1) * ((T + k).choose k : ℝ) := by positivity
      linarith
    · push_neg at hs
      set u := 1 - (k : ℝ) * c / T with hu
      have hu1 : u ≤ 1 := by
        have : 0 ≤ (k : ℝ) * c / T := by positivity
        rw [hu]; linarith
      have hcT : (c : ℝ) / T * T = c := by field_simp
      have e1 : 1 - ((k : ℝ) + 1) * c / T = u - c / T := by rw [hu]; ring
      rw [e1]
      have step : (u - c / T) * (T + c + k + 1) ≤ u * (T + k + 1) := by
        have : (u - c / T) * (T + c + k + 1) = u * (T + k + 1) + (u * c - c / T * T - c / T * (c + k + 1)) := by ring
        rw [this, hcT]
        have h1 : u * c ≤ c := by nlinarith
        have h2 : 0 ≤ (c : ℝ) / T * (c + k + 1) := by positivity
        linarith
      have hupos : 0 ≤ u - c / T := by linarith
      calc (u - c / T) * ((T + c + k + 1) * ((T + c + k).choose k : ℝ))
          = ((u - c / T) * (T + c + k + 1)) * ((T + c + k).choose k : ℝ) := by ring
        _ ≤ (u * (T + k + 1)) * ((T + c + k).choose k : ℝ) := mul_le_mul_of_nonneg_right step hBn
        _ = (T + k + 1) * (u * ((T + c + k).choose k : ℝ)) := by ring
        _ ≤ (T + k + 1) * ((T + k).choose k : ℝ) := mul_le_mul_of_nonneg_left ih (by positivity)

end CountPf

end ReciprocityTheory.ChartRestriction.G.AR.Up
