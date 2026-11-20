import Mathlib

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

/- English proof (translation)
Establish `hDr : (0 : ℝ) < D` using `by exact_mod_cast hD`. Establish `hMr : (0 : ℝ) < M` using `by exact_mod_cast hM`. Take `⟨a, ha⟩ : ∃ a : ℝ, a = 2 * D * M` from `⟨_, rfl⟩`. Establish `ha0 : 0 < a` using `by rw [ha]; positivity`. Take `⟨q, hq⟩ : ∃ q : ℝ, q = Real.exp (-a)` from `⟨_, rfl⟩`.

Establish `hq0 : 0 ≤ q` using `by rw [hq]; exact (Real.exp_pos _).le`. Establish `hq1 : q < 1` using `by rw [hq, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)`. Establish `h1q : 0 < 1 - q` using `by linarith`. Take `⟨K, hK⟩ : ∃ K : ℝ, K = max C 0` from `⟨_, rfl⟩`. Establish `hK0 : 0 ≤ K` using `by rw [hK]; exact le_max_right _ _`.

Establish `hCK : C ≤ K` using `by rw [hK]; exact le_max_left _ _`. Use `⟨K * Real.exp (-a * x₀) / (1 - q), fun r hr => ?_⟩` and prove the remaining obligations. Take `⟨n₀, hn₀⟩ : ∃ n₀ : ℤ, n₀ = ⌈x₀ - Real.log r⌉` from `⟨_, rfl⟩`. Establish `hn₀le : x₀ - Real.log r ≤ n₀` using `by rw [hn₀]; exact Int.le_ceil _`. Establish `hr2 : (0 : ℝ) < r ^ (2 * D)` using `by positivity`.

Take `⟨A, hA⟩ : ∃ A : ℝ, A = K * r ^ (2 * D) * Real.exp (-a * n₀)` from `⟨_, rfl⟩`. Establish `hA0 : 0 ≤ A` using `by rw [hA]; have := Real.exp_pos (-a * n₀); positivity`. Establish `hsupp : Function.support (fun j : ℤ => (if (j : ℝ) + Real.log r < x₀ then 0 else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) * ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ))))) ⊆ Set.range (fun n : ℕ => n₀ + (n : ℤ))`. Introduce `j hj`. Establish `hnot : ¬ ((j : ℝ) + Real.log r < x₀)`.

Introduce `h`. Apply `hj` to reduce the goal to its premises. Simplify using `[h]`. Establish `hge : n₀ ≤ j`. Rewrite using `[hn₀]`.

Apply `Int.ceil_le.mpr` to reduce the goal to its premises. Combine the linear relations using `[not_lt.mp hnot]`. Use `⟨(j - n₀).toNat, ?_⟩` and prove the remaining obligations. Establish `: (((j - n₀).toNat : ℕ) : ℤ) = j - n₀` using `Int.toNat_of_nonneg (by omega)`. Simplify using `only [this]`.

Use linear arithmetic over natural numbers and integers. Establish `hinj : Function.Injective (fun n : ℕ => n₀ + (n : ℤ))`. Introduce `m n h`. Simplify using `using h`. Rewrite using `[← hinj.tsum_eq hsupp]`.

Establish `hterm : ∀ n : ℕ, (if (((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r < x₀ then 0 else ENNReal.ofReal (C * Real.exp (2 * D * ((((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r)))) * ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (((n₀ + (n : ℤ) : ℤ)) : ℝ)))) ≤ ENNReal.ofReal (A * q ^ n)`. Introduce `n`. Use `split_ifs with h`. Simplify using the standard rewrite rules. Rewrite using `[← ENNReal.ofReal_mul' (Real.exp_pos _).le]`.

Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `hr' : r ^ (2 * D) = Real.exp (((2 * D : ℕ) : ℝ) * Real.log r)`. Rewrite using `[Real.exp_nat_mul, Real.exp_log hr]`. Establish `hq' : q ^ n = Real.exp ((n : ℝ) * (-a))`. Rewrite using `[hq, Real.exp_nat_mul]`.

Establish `key : Real.exp (2 * D * ((((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r)) * Real.exp (-(2 * D * (M + 1) * (((n₀ + (n : ℤ) : ℤ)) : ℝ))) = r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n`. Rewrite using `[hr', hq', ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ha]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hpos : 0 ≤ r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n`. Use `Real.exp_pos (-a * n₀)` as an intermediate fact. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation. Use `(ENNReal.tsum_le_tsum hterm).trans ?_` and prove the remaining obligations.

Establish `hsum : Summable (fun n : ℕ => A * q ^ n)` using `(summable_geometric_of_lt_one hq0 hq1).mul_left A`. Rewrite using `[← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite using `[tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]`. Establish `hexp : Real.exp (-a * n₀) ≤ Real.exp (-a * x₀) * r ^ (2 * D * M)`.

Establish `hr' : r ^ (2 * D * M) = Real.exp (((2 * D * M : ℕ) : ℝ) * Real.log r)`. Rewrite using `[Real.exp_nat_mul, Real.exp_log hr]`. Rewrite using `[hr', ← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hc : (((2 * D * M : ℕ) : ℝ)) = a` using `by rw [ha]; push_cast; ring`.

Rewrite using `[hc]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hn₀le ha0.le]`. Establish `hpow : r ^ (2 * D * (M + 1)) = r ^ (2 * D) * r ^ (2 * D * M)`. Rewrite using `[← pow_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hAle : A ≤ K * Real.exp (-a * x₀) * r ^ (2 * D * (M + 1))`. Rewrite using `[hA, hpow]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem geom_sum_int_le (D M : ℕ) (hD : 0 < D) (hM : 1 ≤ M) (x₀ C : ℝ) :
    ∃ C' : ℝ, ∀ r : ℝ, 0 < r →
      ∑' j : ℤ, (if (j : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ)))) ≤
        ENNReal.ofReal (C' * r ^ (2 * D * (M + 1))) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * D * M := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.exp (-a) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact (Real.exp_pos _).le
  have hq1 : q < 1 := by rw [hq, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h1q : 0 < 1 - q := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max C 0 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; exact le_max_right _ _
  have hCK : C ≤ K := by rw [hK]; exact le_max_left _ _
  refine ⟨K * Real.exp (-a * x₀) / (1 - q), fun r hr => ?_⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℤ, n₀ = ⌈x₀ - Real.log r⌉ := ⟨_, rfl⟩
  have hn₀le : x₀ - Real.log r ≤ n₀ := by rw [hn₀]; exact Int.le_ceil _
  have hr2 : (0 : ℝ) < r ^ (2 * D) := by positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = K * r ^ (2 * D) * Real.exp (-a * n₀) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; have := Real.exp_pos (-a * n₀); positivity

  have hsupp : Function.support (fun j : ℤ =>
      (if (j : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ))))) ⊆
      Set.range (fun n : ℕ => n₀ + (n : ℤ)) := by
    intro j hj
    have hnot : ¬ ((j : ℝ) + Real.log r < x₀) := by
      intro h
      apply hj
      simp [h]
    have hge : n₀ ≤ j := by
      rw [hn₀]
      apply Int.ceil_le.mpr
      linarith [not_lt.mp hnot]
    refine ⟨(j - n₀).toNat, ?_⟩
    have : (((j - n₀).toNat : ℕ) : ℤ) = j - n₀ := Int.toNat_of_nonneg (by omega)
    simp only [this]
    omega
  have hinj : Function.Injective (fun n : ℕ => n₀ + (n : ℤ)) := by
    intro m n h
    simpa using h
  rw [← hinj.tsum_eq hsupp]

  have hterm : ∀ n : ℕ,
      (if (((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (((n₀ + (n : ℤ) : ℤ)) : ℝ)))) ≤
        ENNReal.ofReal (A * q ^ n) := by
    intro n
    split_ifs with h
    · simp
    · rw [← ENNReal.ofReal_mul' (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      have hr' : r ^ (2 * D) = Real.exp (((2 * D : ℕ) : ℝ) * Real.log r) := by
        rw [Real.exp_nat_mul, Real.exp_log hr]
      have hq' : q ^ n = Real.exp ((n : ℝ) * (-a)) := by
        rw [hq, Real.exp_nat_mul]
      have key : Real.exp (2 * D * ((((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r)) *
          Real.exp (-(2 * D * (M + 1) * (((n₀ + (n : ℤ) : ℤ)) : ℝ))) =
          r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n := by
        rw [hr', hq', ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ha]
        congr 1
        push_cast
        ring
      have hpos : 0 ≤ r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n := by
        have := Real.exp_pos (-a * n₀)
        positivity
      calc C * Real.exp (2 * D * ((((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r)) *
            Real.exp (-(2 * D * (M + 1) * (((n₀ + (n : ℤ) : ℤ)) : ℝ)))
          = C * (r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n) := by rw [mul_assoc, key]
        _ ≤ K * (r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n) :=
            mul_le_mul_of_nonneg_right hCK hpos
        _ = A * q ^ n := by rw [hA]; ring
  refine (ENNReal.tsum_le_tsum hterm).trans ?_
  have hsum : Summable (fun n : ℕ => A * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left A
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
  apply ENNReal.ofReal_le_ofReal
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]

  have hexp : Real.exp (-a * n₀) ≤ Real.exp (-a * x₀) * r ^ (2 * D * M) := by
    have hr' : r ^ (2 * D * M) = Real.exp (((2 * D * M : ℕ) : ℝ) * Real.log r) := by
      rw [Real.exp_nat_mul, Real.exp_log hr]
    rw [hr', ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc : (((2 * D * M : ℕ) : ℝ)) = a := by rw [ha]; push_cast; ring
    rw [hc]
    nlinarith [mul_le_mul_of_nonneg_left hn₀le ha0.le]
  have hpow : r ^ (2 * D * (M + 1)) = r ^ (2 * D) * r ^ (2 * D * M) := by
    rw [← pow_add]
    congr 1
    ring
  have hAle : A ≤ K * Real.exp (-a * x₀) * r ^ (2 * D * (M + 1)) := by
    rw [hA, hpow]
    calc K * r ^ (2 * D) * Real.exp (-a * n₀)
        ≤ K * r ^ (2 * D) * (Real.exp (-a * x₀) * r ^ (2 * D * M)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = K * Real.exp (-a * x₀) * (r ^ (2 * D) * r ^ (2 * D * M)) := by ring
  calc A * (1 - q)⁻¹
      ≤ (K * Real.exp (-a * x₀) * r ^ (2 * D * (M + 1))) * (1 - q)⁻¹ :=
        mul_le_mul_of_nonneg_right hAle (inv_nonneg.mpr h1q.le)
    _ = K * Real.exp (-a * x₀) / (1 - q) * r ^ (2 * D * (M + 1)) := by
        rw [div_eq_mul_inv]; ring

/- English proof (translation)
Introduce `D M hD hM x₀ C` and use `geom_sum_int_le D M hD hM x₀ C`.
-/
theorem geom_sum_int :
    ∀ (D M : ℕ), 0 < D → 1 ≤ M → ∀ (x₀ C : ℝ), ∃ C' : ℝ, ∀ r : ℝ, 0 < r →
      ∑' j : ℤ, (if (j : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ)))) ≤
        ENNReal.ofReal (C' * r ^ (2 * D * (M + 1))) :=
  fun D M hD hM x₀ C => geom_sum_int_le D M hD hM x₀ C

end GlobalTheory.CompanionTheory.Adelic
