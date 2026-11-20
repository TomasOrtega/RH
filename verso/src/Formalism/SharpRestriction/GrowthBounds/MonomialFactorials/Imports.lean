import Mathlib

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Finset

/- English proof (translation)
Establish `hS1 : ∑ a ∈ A, ∑ w ∈ Wn, ∑ z ∈ I, bl a w z ≤ ∑ a ∈ A, ∑ z ∈ I, (Wn.card : ℝ) * (bq a z * dx z + ε₂ * (dy a z * dx z))`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `a ha`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_le_sum fun z hz => hplus a ha z hz`.

Establish `hQ : ∑ a ∈ A, ∑ z ∈ I, bq a z * dx z ≤ ε₁ * T.card * K * ∑ a ∈ A, m a`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `z _`. Rewrite using `[Finset.sum_mul]`.

Use `_ ≤ ∑ z ∈ I, (ε₁ * ∑ i ∈ T, ∑ a ∈ A, dy (u a i) z) * dx z := by`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `z hz`. Conclude with `mul_le_mul_of_nonneg_right (htm z hz) (hdx z)`. Use `_ = ∑ z ∈ I, ∑ i ∈ T, ∑ a ∈ A, ε₁ * (dy (u a i) z * dx z) := by`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `z _`. Rewrite using `[mul_assoc, Finset.sum_mul, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Use `_ = ∑ i ∈ T, ∑ z ∈ I, ∑ a ∈ A, ε₁ * (dy (u a i) z * dx z) := Finset.sum_comm`. Use `_ = ∑ i ∈ T, ∑ a ∈ A, ∑ z ∈ I, ε₁ * (dy (u a i) z * dx z) := Finset.sum_congr rfl fun i _ => Finset.sum_comm`. Use `_ ≤ ∑ i ∈ T, ∑ a ∈ A, ε₁ * (K * m a) := by`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `i hi`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `a ha`. Rewrite using `[← Finset.mul_sum]`. Apply `mul_le_mul_of_nonneg_left _ h1` to reduce the goal to its premises.

Conclude with `(hcnt (u a i) (hu a ha i hi).1).trans (hu a ha i hi).2`. Use `_ = ∑ i ∈ T, ε₁ * (K * ∑ a ∈ A, m a) := by`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`.

Use `_ = ε₁ * T.card * K * ∑ a ∈ A, m a := by`. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hD : ∑ a ∈ A, ∑ z ∈ I, ε₂ * (dy a z * dx z) ≤ ε₂ * ∑ a ∈ A, m a`. Rewrite using `[Finset.mul_sum]`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `a ha`. Rewrite using `[← Finset.mul_sum]`. Conclude with `mul_le_mul_of_nonneg_left (hcnt a ha) h2`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]`. Use `_ ≤ (Wn.card : ℝ) * (ε₁ * T.card * K * ∑ a ∈ A, m a + ε₂ * ∑ a ∈ A, m a) := mul_le_mul_of_nonneg_left (add_le_add hQ hD) (Nat.cast_nonneg _)`. Use `_ = (ε₁ * T.card * K + ε₂) * ((Wn.card : ℝ) * ∑ a ∈ A, m a) := by ring`.
-/
theorem assemble {α ι Z : Type*} (A : Finset α) (Wn : Finset ℕ) (I : Finset Z) (T : Finset ι)
    (bl : α → ℕ → Z → ℝ) (bq : α → Z → ℝ) (dx : Z → ℝ) (dy : α → Z → ℝ) (u : α → ι → α) (m : α → ℝ)
    (ε₁ ε₂ K : ℝ) (h1 : 0 ≤ ε₁) (h2 : 0 ≤ ε₂) (hdx : ∀ z, 0 ≤ dx z)
    (hplus : ∀ a ∈ A, ∀ z ∈ I, ∑ w ∈ Wn, bl a w z ≤ (Wn.card : ℝ) * (bq a z * dx z + ε₂ * (dy a z * dx z)))
    (htm : ∀ z ∈ I, ∑ a ∈ A, bq a z ≤ ε₁ * ∑ i ∈ T, ∑ a ∈ A, dy (u a i) z)
    (hcnt : ∀ a ∈ A, ∑ z ∈ I, dy a z * dx z ≤ m a)
    (hu : ∀ a ∈ A, ∀ i ∈ T, u a i ∈ A ∧ m (u a i) ≤ K * m a) :
    ∑ a ∈ A, ∑ w ∈ Wn, ∑ z ∈ I, bl a w z ≤ (ε₁ * T.card * K + ε₂) * ((Wn.card : ℝ) * ∑ a ∈ A, m a) := by
  have hS1 : ∑ a ∈ A, ∑ w ∈ Wn, ∑ z ∈ I, bl a w z ≤
      ∑ a ∈ A, ∑ z ∈ I, (Wn.card : ℝ) * (bq a z * dx z + ε₂ * (dy a z * dx z)) := by
    apply Finset.sum_le_sum
    intro a ha
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun z hz => hplus a ha z hz
  have hQ : ∑ a ∈ A, ∑ z ∈ I, bq a z * dx z ≤ ε₁ * T.card * K * ∑ a ∈ A, m a := by
    calc ∑ a ∈ A, ∑ z ∈ I, bq a z * dx z = ∑ z ∈ I, ∑ a ∈ A, bq a z * dx z := Finset.sum_comm
      _ = ∑ z ∈ I, (∑ a ∈ A, bq a z) * dx z := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.sum_mul]
      _ ≤ ∑ z ∈ I, (ε₁ * ∑ i ∈ T, ∑ a ∈ A, dy (u a i) z) * dx z := by
          apply Finset.sum_le_sum
          intro z hz
          exact mul_le_mul_of_nonneg_right (htm z hz) (hdx z)
      _ = ∑ z ∈ I, ∑ i ∈ T, ∑ a ∈ A, ε₁ * (dy (u a i) z * dx z) := by
          apply Finset.sum_congr rfl
          intro z _
          rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ i ∈ T, ∑ z ∈ I, ∑ a ∈ A, ε₁ * (dy (u a i) z * dx z) := Finset.sum_comm
      _ = ∑ i ∈ T, ∑ a ∈ A, ∑ z ∈ I, ε₁ * (dy (u a i) z * dx z) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ ≤ ∑ i ∈ T, ∑ a ∈ A, ε₁ * (K * m a) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro a ha
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ h1
          exact (hcnt (u a i) (hu a ha i hi).1).trans (hu a ha i hi).2
      _ = ∑ i ∈ T, ε₁ * (K * ∑ a ∈ A, m a) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum, Finset.mul_sum]
      _ = ε₁ * T.card * K * ∑ a ∈ A, m a := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hD : ∑ a ∈ A, ∑ z ∈ I, ε₂ * (dy a z * dx z) ≤ ε₂ * ∑ a ∈ A, m a := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hcnt a ha) h2
  calc ∑ a ∈ A, ∑ w ∈ Wn, ∑ z ∈ I, bl a w z
      ≤ ∑ a ∈ A, ∑ z ∈ I, (Wn.card : ℝ) * (bq a z * dx z + ε₂ * (dy a z * dx z)) := hS1
    _ = (Wn.card : ℝ) * (∑ a ∈ A, ∑ z ∈ I, bq a z * dx z
          + ∑ a ∈ A, ∑ z ∈ I, ε₂ * (dy a z * dx z)) := by
        simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (Wn.card : ℝ) * (ε₁ * T.card * K * ∑ a ∈ A, m a + ε₂ * ∑ a ∈ A, m a) :=
        mul_le_mul_of_nonneg_left (add_le_add hQ hD) (Nat.cast_nonneg _)
    _ = (ε₁ * T.card * K + ε₂) * ((Wn.card : ℝ) * ∑ a ∈ A, m a) := by ring

end Formalism.MainNotions.G.SymmetricFormBlocks
