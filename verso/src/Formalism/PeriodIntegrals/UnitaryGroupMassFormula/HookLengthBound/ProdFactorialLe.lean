import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DetShiftNormOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DiagonalMonomialFactorial

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.HookSteps

/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N]`. Establish `h` using `Finset.sum_range_reflect (fun i => i) N`. Rewrite using `[h, Finset.sum_range_id]`.
-/
theorem sum_rev_eq (N : ℕ) : ∑ i : Fin N, (N - 1 - (i : ℕ)) = N * (N - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N]
  have h := Finset.sum_range_reflect (fun i => i) N
  rw [h, Finset.sum_range_id]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `ih'` using `ih (by omega)`. Rewrite using `[← add_assoc, Nat.factorial_succ, pow_succ]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem factorial_add_le (a k B : ℕ) (h : a + k ≤ B) : (a + k).factorial ≤ a.factorial * B ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (by omega)
    rw [← add_assoc, Nat.factorial_succ, pow_succ]
    calc (a + k + 1) * (a + k).factorial ≤ B * (a.factorial * B ^ k) :=
          Nat.mul_le_mul (by omega) ih'
      _ = a.factorial * (B ^ k * B) := by ring

/- English proof (translation)
Establish `hB : ∀ i : Fin N, ν i + (N - 1 - i) ≤ ν ⟨0, hN⟩ + N` using `fun i => by`. Use `hν (show (⟨0, hN⟩ : Fin N) ≤ i from Nat.zero_le _)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_rev_eq]`.
-/
theorem prod_factorial_le (N : ℕ) (hN : 0 < N) (ν : Fin N → ℕ) (hν : Antitone ν) :
    ∏ i : Fin N, (ν i + (N - 1 - i)).factorial ≤
      (∏ i, (ν i).factorial) * (ν ⟨0, hN⟩ + N) ^ (N * (N - 1) / 2) := by
  have hB : ∀ i : Fin N, ν i + (N - 1 - i) ≤ ν ⟨0, hN⟩ + N := fun i => by
    have := hν (show (⟨0, hN⟩ : Fin N) ≤ i from Nat.zero_le _)
    omega
  calc ∏ i : Fin N, (ν i + (N - 1 - i)).factorial
      ≤ ∏ i : Fin N, ((ν i).factorial * (ν ⟨0, hN⟩ + N) ^ (N - 1 - (i : ℕ))) :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => factorial_add_le _ _ _ (hB i)
    _ = (∏ i, (ν i).factorial) * (ν ⟨0, hN⟩ + N) ^ (N * (N - 1) / 2) := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_rev_eq]

/- English proof (translation)
Unfold `HookBoundOf PI.HookBound`. Introduce `hH N hN ν hν`. Establish `h1` using `PI.HookLower.one_le_cNu ν hν`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `hD : (0 : ℝ) < ∏ l, ((ν l).factorial : ℝ)` using `Finset.prod_pos fun l _ => by exact_mod_cast (ν l).factorial_pos`.

Unfold `PI.cNu at h1 ⊢`. Establish `hF0r : (0 : ℝ) ≤ (fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) : ℝ)`. Use `(one_le_div hD).1 h1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hF0 : (0 : ℚ) ≤ fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν)` using `by exact_mod_cast hF0r`.

Establish `hP : (1 : ℚ) ≤ ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((ν i - ν j + (j - i) : ℕ) : ℚ)`. Combine the equalities or inequalities in the displayed calculation. Establish `hij' : i < j` using `Finset.mem_Ioi.1 hj`. Establish `hij : (i : ℕ) < j` using `hij'`. Conclude with `(show 1 ≤ ν i - ν j + (j - i) by omega)` after adjusting the coercions.

Establish `hQ` using `hH N ν hν`. Establish `hFQ : fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) ≤ ∏ i : Fin N, (((ν i + (N - 1 - i)).factorial : ℕ) : ℚ)`. Rewrite using `[← hQ]`. Conclude with `le_mul_of_one_le_right hF0 hP`. Establish `hFQr : (fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) : ℝ) ≤ ∏ i : Fin N, (((ν i + (N - 1 - i)).factorial : ℕ) : ℝ)` using `by exact_mod_cast hFQ`.

Establish `hle : (∏ i : Fin N, (((ν i + (N - 1 - i)).factorial : ℕ) : ℝ)) ≤ (∏ i, ((ν i).factorial : ℝ)) * ((ν ⟨0, hN⟩ : ℝ) + N) ^ (N * (N - 1) / 2)`. Conclude with `prod_factorial_le N hN ν hν` after adjusting the coercions. Rewrite using `[div_le_iff₀ hD]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hook_bound : HookBoundOf := by
  unfold HookBoundOf PI.HookBound
  intro hH N hN ν hν
  have h1 := PI.HookLower.one_le_cNu ν hν
  refine ⟨h1, ?_⟩
  have hD : (0 : ℝ) < ∏ l, ((ν l).factorial : ℝ) :=
    Finset.prod_pos fun l _ => by exact_mod_cast (ν l).factorial_pos
  unfold PI.cNu at h1 ⊢
  have hF0r : (0 : ℝ) ≤ (fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) : ℝ) := by
    have := (one_le_div hD).1 h1
    linarith
  have hF0 : (0 : ℚ) ≤ fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) := by exact_mod_cast hF0r
  have hP : (1 : ℚ) ≤ ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((ν i - ν j + (j - i) : ℕ) : ℚ) := by
    calc (1 : ℚ) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (1 : ℚ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by positivity) fun i _ =>
          Finset.prod_le_prod (fun _ _ => zero_le_one) fun j hj => by
            have hij' : i < j := Finset.mem_Ioi.1 hj
            have hij : (i : ℕ) < j := hij'
            exact_mod_cast (show 1 ≤ ν i - ν j + (j - i) by omega)
  have hQ := hH N ν hν
  have hFQ : fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) ≤
      ∏ i : Fin N, (((ν i + (N - 1 - i)).factorial : ℕ) : ℚ) := by
    rw [← hQ]
    exact le_mul_of_one_le_right hF0 hP
  have hFQr : (fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) : ℝ) ≤
      ∏ i : Fin N, (((ν i + (N - 1 - i)).factorial : ℕ) : ℝ) := by exact_mod_cast hFQ
  have hle : (∏ i : Fin N, (((ν i + (N - 1 - i)).factorial : ℕ) : ℝ)) ≤
      (∏ i, ((ν i).factorial : ℝ)) * ((ν ⟨0, hN⟩ : ℝ) + N) ^ (N * (N - 1) / 2) := by
    exact_mod_cast prod_factorial_le N hN ν hν
  rw [div_le_iff₀ hD]
  linarith

end PI.HookSteps
