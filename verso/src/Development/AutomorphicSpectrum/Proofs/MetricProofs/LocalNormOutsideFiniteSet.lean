import Mathlib

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.LogLin

/- English proof (translation)
Introduce `C n K hC hn hK`. Take `⟨A, hA⟩ : ∃ A : ℝ, A = 2 + 2 * C + n` from `⟨_, rfl⟩`. Establish `hA0 : 0 < A` using `by rw [hA]; linarith`. Establish `hCA : 0 ≤ C * A` using `mul_nonneg hC hA0.le`. Take `⟨D, hD⟩ : ∃ D : ℝ, D = 1 + K + C + 2 * (C * A + C)` from `⟨_, rfl⟩`.

Use `⟨D, by rw [hD]; linarith, by rw [hD]; linarith, ?_⟩` and prove the remaining obligations. Introduce `x y hx hy`. Take `⟨u, hu⟩ : ∃ u : ℝ, u = 2 + D + x` from `⟨_, rfl⟩`. Rewrite using `[← hu]`. Establish `ht : 0 ≤ x + K` using `by linarith`.

Establish `hut : 2 + (x + K) ≤ u` using `by rw [hu, hD]; linarith`. Establish `hu2 : 2 ≤ u` using `by linarith`. Establish `hnK : 0 ≤ n * K` using `mul_nonneg hn hK`. Establish `hnt : 0 ≤ n * (x + K)` using `mul_nonneg hn ht`. Establish `hmax : max y 0 ≤ n * (x + K) + C` using `max_le (by nlinarith) (by linarith)`.

Establish `hm0 : 0 ≤ max y 0` using `le_max_right _ _`. Establish `h1 : n * (x + K) ≤ n * u` using `mul_le_mul_of_nonneg_left (by linarith) hn`. Establish `h2 : C * 1 ≤ C * u` using `mul_le_mul_of_nonneg_left (by linarith) hC`. Establish `hle : 2 + C + max y 0 ≤ A * u` using `by rw [hA]; nlinarith`. Establish `hlog : Real.log (2 + C + max y 0) ≤ Real.log A + Real.log u`.

Rewrite using `[← Real.log_mul hA0.ne' (by linarith)]`. Conclude with `Real.log_le_log (by linarith) hle`. Establish `hlA : Real.log A ≤ A` using `(Real.log_le_sub_one_of_pos hA0).trans (by linarith)`. Establish `hlu : 1 / 2 ≤ Real.log u`. Establish `h` using `Real.log_le_log (by norm_num : (0:ℝ) < 2) hu2`.

Establish `h'` using `Real.log_two_gt_d9`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : C * Real.log (2 + C + max y 0) ≤ C * (A + Real.log u)` using `mul_le_mul_of_nonneg_left (by linarith) hC`. Establish `h4 : 2 * (C * A + C) * (1 / 2) ≤ 2 * (C * A + C) * Real.log u` using `mul_le_mul_of_nonneg_left hlu (by linarith)`. Establish `h5 : 0 ≤ (1 + K) * Real.log u` using `mul_nonneg (by linarith) (by linarith)`.

Rewrite using `[hD]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_log_affine_le : ∀ C n K : ℝ, 0 ≤ C → 0 ≤ n → 0 ≤ K → ∃ C₁ : ℝ, 1 ≤ C₁ ∧ K ≤ C₁ ∧ ∀ x y : ℝ, -K ≤ x → y ≤ n * x + C → C * Real.log (2 + C + max y 0) + C ≤ C₁ * Real.log (2 + C₁ + x) := by
  intro C n K hC hn hK
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 + 2 * C + n := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; linarith
  have hCA : 0 ≤ C * A := mul_nonneg hC hA0.le
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 1 + K + C + 2 * (C * A + C) := ⟨_, rfl⟩
  refine ⟨D, by rw [hD]; linarith, by rw [hD]; linarith, ?_⟩
  intro x y hx hy
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 2 + D + x := ⟨_, rfl⟩
  rw [← hu]
  have ht : 0 ≤ x + K := by linarith
  have hut : 2 + (x + K) ≤ u := by rw [hu, hD]; linarith
  have hu2 : 2 ≤ u := by linarith
  have hnK : 0 ≤ n * K := mul_nonneg hn hK
  have hnt : 0 ≤ n * (x + K) := mul_nonneg hn ht
  have hmax : max y 0 ≤ n * (x + K) + C := max_le (by nlinarith) (by linarith)
  have hm0 : 0 ≤ max y 0 := le_max_right _ _
  have h1 : n * (x + K) ≤ n * u := mul_le_mul_of_nonneg_left (by linarith) hn
  have h2 : C * 1 ≤ C * u := mul_le_mul_of_nonneg_left (by linarith) hC
  have hle : 2 + C + max y 0 ≤ A * u := by rw [hA]; nlinarith
  have hlog : Real.log (2 + C + max y 0) ≤ Real.log A + Real.log u := by
    rw [← Real.log_mul hA0.ne' (by linarith)]
    exact Real.log_le_log (by linarith) hle
  have hlA : Real.log A ≤ A := (Real.log_le_sub_one_of_pos hA0).trans (by linarith)
  have hlu : 1 / 2 ≤ Real.log u := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 2) hu2
    have h' := Real.log_two_gt_d9
    linarith
  have h3 : C * Real.log (2 + C + max y 0) ≤ C * (A + Real.log u) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  have h4 : 2 * (C * A + C) * (1 / 2) ≤ 2 * (C * A + C) * Real.log u :=
    mul_le_mul_of_nonneg_left hlu (by linarith)
  have h5 : 0 ≤ (1 + K) * Real.log u := mul_nonneg (by linarith) (by linarith)
  rw [hD]
  nlinarith

end GlobalTheory.CompanionTheory.LogLin
