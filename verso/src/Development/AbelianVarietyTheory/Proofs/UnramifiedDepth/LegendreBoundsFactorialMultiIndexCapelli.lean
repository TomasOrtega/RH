import Mathlib
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation

open ReciprocityTheory.PGsh

namespace GlobalTheory.LegendreBounds

/- English proof (translation)
Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Simplify using the standard rewrite rules. Establish `hlen : (Nat.digits l N).length = Nat.log l N + 1` using `Nat.length_digits l N hl hN.ne'`. Establish `hd : ∀ d ∈ Nat.digits l N, d ≤ l - 1` using `fun d hd => by`. Use `Nat.digits_lt_base hl hd` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation. Simplify `List.sum_le_card_nsmul _ _ hd` using `[smul_eq_mul]`. Use `_ = (Nat.log l N + 1) * (l - 1) := by rw [hlen]`.
-/
theorem digitSum_le (l N : ℕ) (hl : 1 < l) :
    (Nat.digits l N).sum ≤ (Nat.log l N + 1) * (l - 1) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hlen : (Nat.digits l N).length = Nat.log l N + 1 := Nat.length_digits l N hl hN.ne'
    have hd : ∀ d ∈ Nat.digits l N, d ≤ l - 1 := fun d hd => by
      have := Nat.digits_lt_base hl hd
      omega
    calc (Nat.digits l N).sum ≤ (Nat.digits l N).length * (l - 1) := by
          simpa [smul_eq_mul] using List.sum_le_card_nsmul _ _ hd
      _ = (Nat.log l N + 1) * (l - 1) := by rw [hlen]

/- English proof (translation)
Use `Fact.mk hl` as an intermediate fact. Establish `h1 : (l - 1) * padicValNat l N.factorial = N - (Nat.digits l N).sum` using `sub_one_mul_padicValNat_factorial N`. Establish `h2 : (Nat.digits l N).sum ≤ N` using `Nat.digit_sum_le l N`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hl.one_lt`. Establish `h3` using `congrArg (Nat.cast : ℕ → ℝ) h1`.

Rewrite `h3` using `[Nat.cast_mul, Nat.cast_sub hl.one_le, Nat.cast_sub h2, Nat.cast_one]`. Rewrite using `[eq_div_iff (by linarith)]`. Take the linear combination `h3`.
-/
theorem legendre_real (l : ℕ) (hl : l.Prime) (N : ℕ) :
    (padicValNat l N.factorial : ℝ) = ((N : ℝ) - ((Nat.digits l N).sum : ℕ)) / (l - 1) := by
  have := Fact.mk hl
  have h1 : (l - 1) * padicValNat l N.factorial = N - (Nat.digits l N).sum :=
    sub_one_mul_padicValNat_factorial N
  have h2 : (Nat.digits l N).sum ≤ N := Nat.digit_sum_le l N
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have h3 := congrArg (Nat.cast : ℕ → ℝ) h1
  rw [Nat.cast_mul, Nat.cast_sub hl.one_le, Nat.cast_sub h2, Nat.cast_one] at h3
  rw [eq_div_iff (by linarith)]
  linear_combination h3

/- English proof (translation)
Establish `hl1 : (0 : ℝ) < l - 1`. Establish `: (1 : ℝ) < l` using `by exact_mod_cast hl`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[div_le_iff₀ hl1]`. Establish `h` using `digitSum_le l N hl`.

Establish `h' : ((Nat.digits l N).sum : ℝ) ≤ ((Nat.log l N + 1) * (l - 1) : ℕ)` using `by exact_mod_cast h`. Rewrite `h'` using `[Nat.cast_mul, Nat.cast_add, Nat.cast_sub hl.le, Nat.cast_one]`. Conclude with `h'`.
-/
private theorem digits_sum_div_pred_le_log_add_one (l N : ℕ) (hl : 1 < l) :
    ((Nat.digits l N).sum : ℝ) / (l - 1) ≤ Nat.log l N + 1 := by
  have hl1 : (0 : ℝ) < l - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl
    linarith
  rw [div_le_iff₀ hl1]
  have h := digitSum_le l N hl
  have h' : ((Nat.digits l N).sum : ℝ) ≤ ((Nat.log l N + 1) * (l - 1) : ℕ) := by exact_mod_cast h
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hl.le, Nat.cast_one] at h'
  exact h'

/- English proof (translation)
Establish `hl' : (1 : ℝ) < l` using `by exact_mod_cast hl`. Establish `hM' : (0 : ℝ) < M` using `by exact_mod_cast hM`. Rewrite using `[Real.le_logb_iff_rpow_le hl' hM', Real.rpow_natCast]`. Establish `: l ^ Nat.log l N ≤ M`. Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases.

Simplify using `using hM`. Conclude with `(Nat.pow_log_le_self l hN.ne').trans hNM`. Conclude with `this` after adjusting the coercions.
-/
private theorem natLog_le_logb_of_le (l N M : ℕ) (hl : 1 < l) (hM : 1 ≤ M) (hNM : N ≤ M) :
    (Nat.log l N : ℝ) ≤ Real.logb l M := by
  have hl' : (1 : ℝ) < l := by exact_mod_cast hl
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [Real.le_logb_iff_rpow_le hl' hM', Real.rpow_natCast]
  have : l ^ Nat.log l N ≤ M := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simpa using hM
    · exact (Nat.pow_log_le_self l hN.ne').trans hNM
  exact_mod_cast this

/- English proof (translation)
Establish `h1` using `digits_sum_div_pred_le_log_add_one l N hl.one_lt`. Establish `h2` using `natLog_le_logb_of_le l N M hl.one_lt hM hNM`. Rewrite using `[legendre_real l hl N, sub_div]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lower (l : ℕ) (hl : l.Prime) (N M : ℕ) (hM : 1 ≤ M) (hNM : N ≤ M) :
    (N : ℝ) / (l - 1) - (Real.logb l M + 1) ≤ padicValNat l N.factorial := by
  have h1 := digits_sum_div_pred_le_log_add_one l N hl.one_lt
  have h2 := natLog_le_logb_of_le l N M hl.one_lt hM hNM
  rw [legendre_real l hl N, sub_div]
  linarith

/- English proof (translation)
Establish `hl1 : (0 : ℝ) < l - 1`. Establish `: (1 : ℝ) < l` using `by exact_mod_cast hl.one_lt`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[legendre_real l hl N, div_le_div_iff_of_pos_right hl1]`. Establish `: (0 : ℝ) ≤ ((Nat.digits l N).sum : ℕ)` using `Nat.cast_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem upper (l : ℕ) (hl : l.Prime) (N : ℕ) :
    (padicValNat l N.factorial : ℝ) ≤ (N : ℝ) / (l - 1) := by
  have hl1 : (0 : ℝ) < l - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    linarith
  rw [legendre_real l hl N, div_le_div_iff_of_pos_right hl1]
  have : (0 : ℝ) ≤ ((Nat.digits l N).sum : ℕ) := Nat.cast_nonneg _
  linarith

/- English proof (translation)
Establish `hl1 : (0 : ℝ) < l - 1`. Establish `: (1 : ℝ) < l` using `by exact_mod_cast hl.one_lt`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN0 : N ≠ 0` using `by omega`. Establish `hs : 1 ≤ (Nat.digits l N).sum`.

Establish `hmem` using `List.getLast_mem ((Nat.digits_ne_nil_iff_ne_zero (b := l) (n := N)).mpr hN0)`. Establish `hlast` using `Nat.getLast_digit_ne_zero l hN0`. Use `List.le_sum_of_mem hmem` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hs' : (1 : ℝ) ≤ ((Nat.digits l N).sum : ℕ)` using `by exact_mod_cast hs`.

Rewrite using `[legendre_real l hl N, div_le_div_iff_of_pos_right hl1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem upper_of_pos (l : ℕ) (hl : l.Prime) (N : ℕ) (hN : 1 ≤ N) :
    (padicValNat l N.factorial : ℝ) ≤ ((N : ℝ) - 1) / (l - 1) := by
  have hl1 : (0 : ℝ) < l - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    linarith
  have hN0 : N ≠ 0 := by omega
  have hs : 1 ≤ (Nat.digits l N).sum := by
    have hmem := List.getLast_mem ((Nat.digits_ne_nil_iff_ne_zero (b := l) (n := N)).mpr hN0)
    have hlast := Nat.getLast_digit_ne_zero l hN0
    have := List.le_sum_of_mem hmem
    omega
  have hs' : (1 : ℝ) ≤ ((Nat.digits l N).sum : ℕ) := by exact_mod_cast hs
  rw [legendre_real l hl N, div_le_div_iff_of_pos_right hl1]
  linarith

/- English proof (translation)
Use `Fact.mk hl` as an intermediate fact. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `a t ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, padicValNat.mul (Nat.factorial_ne_zero _) (Finset.prod_ne_zero_iff.mpr fun j _ => Nat.factorial_ne_zero _), Nat.cast_add, ih]`.
-/
theorem padicValNat_prod_factorial (l : ℕ) (hl : l.Prime) {κ : Type} (s : Finset κ)
    (A : κ → ℕ) :
    (padicValNat l (∏ j ∈ s, (A j).factorial) : ℝ)
      = ∑ j ∈ s, (padicValNat l (A j).factorial : ℝ) := by
  have := Fact.mk hl
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValNat.mul (Nat.factorial_ne_zero _)
        (Finset.prod_ne_zero_iff.mpr fun j _ => Nat.factorial_ne_zero _), Nat.cast_add, ih]

/- English proof (translation)
Introduce `l hl`. Use `⟨fun N hN => ⟨lower l hl N N hN le_rfl, upper_of_pos l hl N hN⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `κ _ A hA`. Rewrite using `[padicValNat_prod_factorial l hl Finset.univ A]`. Establish `key : ∀ j ∈ (Finset.univ : Finset κ), (A j : ℝ) / (l - 1) - (Real.logb l ((∑ i, A i : ℕ) : ℝ) + 1) ≤ padicValNat l (A j).factorial` using `fun j _ => lower l hl (A j) (∑ i, A i) hA (Finset.single_le_sum (fun i _ => Nat.zero_le (A i)) (Finset.mem_univ j))`.

Establish `h` using `Finset.sum_le_sum key`. Rewrite `h` using `[Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div, ← Nat.cast_sum]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `n₀ x`. Break down `Nat.eq_zero_or_pos n₀ with rfl | hn` into its components or cases.

Simplify using the standard rewrite rules. Establish `e1` using `padicValNat_prod_factorial l hl (Finset.range n₀) (fun c => x + c)`. Establish `e2` using `padicValNat_prod_factorial l hl (Finset.range n₀) (fun c => c)`. Rewrite using `[e1, e2, ← Finset.sum_sub_distrib]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h1` using `upper l hl (x + c)`. Establish `h2` using `lower l hl c n₀ hn (Finset.mem_range.mp hc).le`. Move the coercions through the operations in `at h1`. Establish `h3 : ((x : ℝ) + c) / (l - 1) = x / (l - 1) + c / (l - 1)` using `add_div _ _ _`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `_ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring`.
-/
theorem legendre_bounds :
  (∀ (l : ℕ), l.Prime → (∀ N : ℕ, 1 ≤ N → (N : ℝ) / (l - 1) - (Real.logb l N + 1) ≤ padicValNat l N.factorial ∧ (padicValNat l N.factorial : ℝ) ≤ (N - 1) / (l - 1)) ∧
    (∀ (κ : Type) [Fintype κ] (A : κ → ℕ), 1 ≤ ∑ j, A j → ((∑ j, A j : ℕ) : ℝ) / (l - 1) - Fintype.card κ * (Real.logb l ((∑ j, A j : ℕ) : ℝ) + 1) ≤ padicValNat l (∏ j, (A j).factorial)) ∧
    ∀ n₀ x : ℕ, (padicValNat l (∏ c ∈ Finset.range n₀, (x + c).factorial) : ℝ) - padicValNat l (∏ c ∈ Finset.range n₀, c.factorial) ≤
      n₀ * x / (l - 1) + n₀ * (Real.logb l n₀ + 1)) := by
  intro l hl
  refine ⟨fun N hN => ⟨lower l hl N N hN le_rfl, upper_of_pos l hl N hN⟩, ?_, ?_⟩
  · intro κ _ A hA
    rw [padicValNat_prod_factorial l hl Finset.univ A]
    have key : ∀ j ∈ (Finset.univ : Finset κ), (A j : ℝ) / (l - 1) - (Real.logb l ((∑ i, A i : ℕ) : ℝ) + 1)
        ≤ padicValNat l (A j).factorial := fun j _ =>
      lower l hl (A j) (∑ i, A i) hA
        (Finset.single_le_sum (fun i _ => Nat.zero_le (A i)) (Finset.mem_univ j))
    have h := Finset.sum_le_sum key
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div,
      ← Nat.cast_sum] at h
    linarith
  · intro n₀ x
    rcases Nat.eq_zero_or_pos n₀ with rfl | hn
    · simp
    · have e1 := padicValNat_prod_factorial l hl (Finset.range n₀) (fun c => x + c)
      have e2 := padicValNat_prod_factorial l hl (Finset.range n₀) (fun c => c)
      rw [e1, e2, ← Finset.sum_sub_distrib]
      calc _ ≤ ∑ c ∈ Finset.range n₀, ((x : ℝ) / (l - 1) + (Real.logb l n₀ + 1)) :=
            Finset.sum_le_sum fun c hc => by
              have h1 := upper l hl (x + c)
              have h2 := lower l hl c n₀ hn (Finset.mem_range.mp hc).le
              push_cast at h1
              have h3 : ((x : ℝ) + c) / (l - 1) = x / (l - 1) + c / (l - 1) := add_div _ _ _
              linarith
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end GlobalTheory.LegendreBounds
