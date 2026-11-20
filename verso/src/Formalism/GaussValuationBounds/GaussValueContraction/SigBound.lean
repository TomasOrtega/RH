import Formalism.GaussValuationBounds.Statement

namespace Formalism.NOK

/- English proof (translation)
Establish `ha2 : 2 ≤ a` using `by linarith`. Break down `k with _ | k` into its components or cases. Simplify using `only [pow_zero, zero_add, mul_one]`. Establish `: 0 ≤ a ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h1 : a ^ k ≤ L ^ k` using `pow_le_pow_left₀ (by linarith) (by linarith) k`. Establish `h3 : 0 < a ^ 3` using `by positivity`. Establish `hLp : 0 < L` using `by linarith`. Establish `e1 : L * a ^ (k + 1 + 2) = L * a ^ k * a ^ 3` using `by ring`. Establish `e2 : 3 / 2 * L ^ (k + 1) * a ^ 3 = 3 / 2 * L * L ^ k * a ^ 3` using `by ring`.

Rewrite using `[e1, e2]`. Establish `h4 : L * a ^ k * a ^ 3 ≤ L * L ^ k * a ^ 3`. Apply `mul_le_mul_of_nonneg_right _ h3.le` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_left h1 hLp.le`. Establish `h5 : 0 ≤ L * L ^ k * a ^ 3` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sigBound_pow (L a : ℝ) (k : ℕ) (hL : 3 ≤ L) (ha : a = L - 1) :
    L * a ^ (k + 2) ≤ 3 / 2 * L ^ k * a ^ 3 := by
  have ha2 : 2 ≤ a := by linarith
  rcases k with _ | k
  · simp only [pow_zero, zero_add, mul_one]
    have : 0 ≤ a ^ 2 := by positivity
    nlinarith
  · have h1 : a ^ k ≤ L ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
    have h3 : 0 < a ^ 3 := by positivity
    have hLp : 0 < L := by linarith
    have e1 : L * a ^ (k + 1 + 2) = L * a ^ k * a ^ 3 := by ring
    have e2 : 3 / 2 * L ^ (k + 1) * a ^ 3 = 3 / 2 * L * L ^ k * a ^ 3 := by ring
    rw [e1, e2]
    have h4 : L * a ^ k * a ^ 3 ≤ L * L ^ k * a ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ h3.le
      exact mul_le_mul_of_nonneg_left h1 hLp.le
    have h5 : 0 ≤ L * L ^ k * a ^ 3 := by positivity
    nlinarith

/- English proof (translation)
Introduce `ℓ hℓ g h j hj`. Unfold `sigNOK`. Take `⟨k, rfl⟩ : ∃ k, j = k + 1` from `⟨j - 1, by omega⟩`. Rewrite using `[Nat.add_sub_cancel]`. Establish `hL3 : (3 : ℝ) ≤ (ℓ : ℝ)` using `by exact_mod_cast hℓ`.

Use `set L : ℝ := (ℓ : ℝ) with hL`. Use `set a : ℝ := L - 1 with ha`. Establish `ha2 : 2 ≤ a` using `by linarith`. Establish `hapos : 0 < a` using `by linarith`. Establish `hLpos : 0 < L` using `by linarith`.

Establish `hmle : (((h + 2 * g) / (ℓ - 1) : ℕ) : ℝ) ≤ ((h : ℝ) + 2 * g) / a`. Use `Nat.cast_div_le (α := ℝ) (m := h + 2 * g) (n := ℓ - 1)` as an intermediate fact. Establish `e : ((ℓ - 1 : ℕ) : ℝ) = a`. Rewrite using `[Nat.cast_sub (by omega)]; simp [ha, hL]`. Rewrite `this` using `[e]`.

Move the coercions through the operations in `at this`. Conclude with `this`. Use `set m : ℕ := (h + 2 * g) / (ℓ - 1) with hm`. Use `set H : ℝ := (h : ℝ) + 2 * g with hH`. Establish `hH0 : 0 ≤ H` using `by positivity`.

Establish `hg0 : (0 : ℝ) ≤ g` using `by positivity`. Establish `hm0 : (0 : ℝ) ≤ m` using `by positivity`. Use `set P : ℝ := L ^ k with hP`. Establish `hP1 : 1 ≤ P` using `one_le_pow₀ (by linarith)`. Establish `hPpos : 0 < P` using `by linarith`.

Establish `hpow` using `sigBound_pow L a k hL3 ha`. Establish `hq : L / a ^ 2 ≤ 3 / 4`. Rewrite using `[div_le_iff₀ (by positivity)]; nlinarith`. Establish `t1 : 3 * (g : ℝ) * L / a ^ 2 ≤ 9 / 4 * g`. Use `mul_le_mul_of_nonneg_left hq hg0` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation. Establish `t2 : L / (P * a ^ 2) ≤ 3 / 4`. Combine the equalities or inequalities in the displayed calculation. Apply `div_le_div_of_nonneg_left hLpos.le (by positivity)` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_right hP1 (by positivity)`.

Use `_ = L / a ^ 2 := by ring`. Use `_ ≤ 3 / 4 := hq`. Establish `t3 : H * L / (P * a ^ 3) ≤ 3 / 2 * H / a ^ (k + 1 + 1)`. Rewrite using `[div_le_div_iff₀ (by positivity) (by positivity)]`. Establish `: L * a ^ (k + 2) ≤ 3 / 2 * P * a ^ 3` using `hpow`.

Combine the equalities or inequalities in the displayed calculation. Establish `t4 : (m : ℝ) * L / (P * a ^ 2) ≤ H * L / (P * a ^ 3)`. Establish `e : H * L / (P * a ^ 3) = (H / a) * L / (P * a ^ 2)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Apply `div_le_div_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_right hmle hLpos.le`. Establish `hsplit : (3 * (g : ℝ) + ((m : ℝ) + 1) / P) * L / a ^ 2 = 3 * (g : ℝ) * L / a ^ 2 + (m : ℝ) * L / (P * a ^ 2) + L / (P * a ^ 2)` using `by field_simp; ring`. Establish `hX0 : 0 ≤ (3 * (g : ℝ) + ((m : ℝ) + 1) / P) * L / a ^ 2` using `by positivity`. Establish `hfl` using `Nat.floor_le hX0`.

Use `push_cast`. Rewrite `hfl`, the goal using `[hsplit]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sigBound_proof : SigBound := by
  intro ℓ hℓ g h j hj
  unfold sigNOK
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hL3 : (3 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  set L : ℝ := (ℓ : ℝ) with hL
  set a : ℝ := L - 1 with ha
  have ha2 : 2 ≤ a := by linarith
  have hapos : 0 < a := by linarith
  have hLpos : 0 < L := by linarith
  have hmle : (((h + 2 * g) / (ℓ - 1) : ℕ) : ℝ) ≤ ((h : ℝ) + 2 * g) / a := by
    have := Nat.cast_div_le (α := ℝ) (m := h + 2 * g) (n := ℓ - 1)
    have e : ((ℓ - 1 : ℕ) : ℝ) = a := by
      rw [Nat.cast_sub (by omega)]; simp [ha, hL]
    rw [e] at this; push_cast at this; exact this
  set m : ℕ := (h + 2 * g) / (ℓ - 1) with hm
  set H : ℝ := (h : ℝ) + 2 * g with hH
  have hH0 : 0 ≤ H := by positivity
  have hg0 : (0 : ℝ) ≤ g := by positivity
  have hm0 : (0 : ℝ) ≤ m := by positivity
  set P : ℝ := L ^ k with hP
  have hP1 : 1 ≤ P := one_le_pow₀ (by linarith)
  have hPpos : 0 < P := by linarith
  have hpow := sigBound_pow L a k hL3 ha

  have hq : L / a ^ 2 ≤ 3 / 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have t1 : 3 * (g : ℝ) * L / a ^ 2 ≤ 9 / 4 * g := by
    have := mul_le_mul_of_nonneg_left hq hg0
    calc 3 * (g : ℝ) * L / a ^ 2 = 3 * ((g : ℝ) * (L / a ^ 2)) := by ring
      _ ≤ 9 / 4 * (g : ℝ) := by linarith
  have t2 : L / (P * a ^ 2) ≤ 3 / 4 := by
    calc L / (P * a ^ 2) ≤ L / (1 * a ^ 2) := by
          apply div_le_div_of_nonneg_left hLpos.le (by positivity)
          exact mul_le_mul_of_nonneg_right hP1 (by positivity)
      _ = L / a ^ 2 := by ring
      _ ≤ 3 / 4 := hq
  have t3 : H * L / (P * a ^ 3) ≤ 3 / 2 * H / a ^ (k + 1 + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : L * a ^ (k + 2) ≤ 3 / 2 * P * a ^ 3 := hpow
    calc H * L * a ^ (k + 1 + 1) = H * (L * a ^ (k + 2)) := by ring
      _ ≤ H * (3 / 2 * P * a ^ 3) := mul_le_mul_of_nonneg_left this hH0
      _ = 3 / 2 * H * (P * a ^ 3) := by ring
  have t4 : (m : ℝ) * L / (P * a ^ 2) ≤ H * L / (P * a ^ 3) := by
    have e : H * L / (P * a ^ 3) = (H / a) * L / (P * a ^ 2) := by
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right hmle hLpos.le
  have hsplit : (3 * (g : ℝ) + ((m : ℝ) + 1) / P) * L / a ^ 2 =
      3 * (g : ℝ) * L / a ^ 2 + (m : ℝ) * L / (P * a ^ 2) + L / (P * a ^ 2) := by
    field_simp; ring
  have hX0 : 0 ≤ (3 * (g : ℝ) + ((m : ℝ) + 1) / P) * L / a ^ 2 := by positivity
  have hfl := Nat.floor_le hX0
  push_cast
  rw [hsplit] at hfl ⊢
  linarith

end Formalism.NOK
