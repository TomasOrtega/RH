import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

/- English proof (translation)
Establish `h1' : h.coeff (-1) ≠ 0` using `by rw [h1]; exact one_ne_zero`. Establish `hne : h ≠ 0` using `HahnSeries.ne_zero_of_coeff_ne_zero h1'`. Use `le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1') ?_` and prove the remaining obligations. Conclude with `le_of_not_gt fun hlt => hne (HahnSeries.coeff_order_eq_zero.mp (h0 _ hlt))`.
-/
theorem hahnSeries_order_eq_neg_one_of_coeff {Ω : Type} [Field Ω] {h : HahnSeries ℚ Ω}
    (h1 : h.coeff (-1) = 1) (h0 : ∀ r : ℚ, r < -1 → h.coeff r = 0) : h.order = -1 := by
  have h1' : h.coeff (-1) ≠ 0 := by rw [h1]; exact one_ne_zero
  have hne : h ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1'
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1') ?_
  exact le_of_not_gt fun hlt => hne (HahnSeries.coeff_order_eq_zero.mp (h0 _ hlt))

/- English proof (translation)
Establish `hord : ∀ k : ℕ, (h ^ k).order = -(k : ℚ)` using `fun k => by`. Rewrite using `[HahnSeries.order_pow, ho]`. Simplify using the standard rewrite rules. Use `⟨hord n, ?_⟩` and prove the remaining obligations. Proceed by induction on `n with`.

Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `hm` using `HahnSeries.coeff_mul_order_add_order (h ^ k) h`. Rewrite `hm` using `[HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hord k, ho, ih, h1, mul_one]`. Establish `e : -((k + 1 : ℕ) : ℚ) = -(k : ℚ) + -1` using `by push_cast; ring`.

Rewrite using `[pow_succ, e, hm]`.
-/
theorem hahnSeries_pow_order_of_order_neg_one {Ω : Type} [Field Ω] {h : HahnSeries ℚ Ω}
    (h1 : h.coeff (-1) = 1) (ho : h.order = -1) (n : ℕ) :
    (h ^ n).order = -(n : ℚ) ∧ (h ^ n).coeff (-(n : ℚ)) = 1 := by
  have hord : ∀ k : ℕ, (h ^ k).order = -(k : ℚ) := fun k => by
    rw [HahnSeries.order_pow, ho]
    simp
  refine ⟨hord n, ?_⟩
  induction n with
  | zero => simp
  | succ k ih =>

    have hm := HahnSeries.coeff_mul_order_add_order (h ^ k) h
    rw [HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hord k, ho, ih, h1, mul_one] at hm
    have e : -((k + 1 : ℕ) : ℚ) = -(k : ℚ) + -1 := by push_cast; ring
    rw [pow_succ, e, hm]

/- English proof (translation)
Rewrite using `[Algebra.smul_def, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]`.
-/
private theorem hahnSeries_coeff_algebra_smul {Ω : Type} [Field Ω] [Algebra ℚ Ω] (r : Ω) (y : HahnSeries ℚ Ω) (a : ℚ) :
    (@HSMul.hSMul Ω (HahnSeries ℚ Ω) (HahnSeries ℚ Ω) (@instHSMul _ _ Algebra.toSMul) r y).coeff a =
      r * y.coeff a := by
  rw [Algebra.smul_def, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]

/- English proof (translation)
Unfold `Transcendental IsAlgebraic`. Introduce and unpack `⟨p, hp0, hp⟩`. Take `⟨h1, h0, -⟩` from `X.j_exp`. Establish `ho` using `hahnSeries_order_eq_neg_one_of_coeff h1 h0`. Establish `hz : Polynomial.aeval (X.exp X.jK) p = 0`.

Rewrite using `[Polynomial.aeval_algHom_apply, hp, map_zero]`. Establish `hc : (Polynomial.aeval (X.exp X.jK) p).coeff (-(p.natDegree : ℚ)) = p.leadingCoeff`. Rewrite using `[Polynomial.aeval_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_eq_single p.natDegree]`. Rewrite using `[hahnSeries_coeff_algebra_smul, (hahnSeries_pow_order_of_order_neg_one h1 ho _).2, mul_one]`. Both sides reduce to the same expression.

Introduce `i hi hne`. Establish `hlt : i < p.natDegree` using `lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne`. Establish `hlt' : (i : ℚ) < p.natDegree` using `by exact_mod_cast hlt`. Rewrite using `[hahnSeries_coeff_algebra_smul, HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]`. Rewrite using `[(hahnSeries_pow_order_of_order_neg_one h1 ho i).1]`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `hn`. Conclude with `absurd (Finset.self_mem_range_succ _) hn`. Rewrite `hc` using `[hz, HahnSeries.coeff_zero]`. Conclude with `hp0 (Polynomial.leadingCoeff_eq_zero.mp hc.symm)`.
-/
theorem Tower.jK_transcendental {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) :
    Transcendental Ω X.jK := by
  unfold Transcendental IsAlgebraic
  rintro ⟨p, hp0, hp⟩
  obtain ⟨h1, h0, -⟩ := X.j_exp
  have ho := hahnSeries_order_eq_neg_one_of_coeff h1 h0
  have hz : Polynomial.aeval (X.exp X.jK) p = 0 := by
    rw [Polynomial.aeval_algHom_apply, hp, map_zero]

  have hc : (Polynomial.aeval (X.exp X.jK) p).coeff (-(p.natDegree : ℚ)) = p.leadingCoeff := by
    rw [Polynomial.aeval_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_eq_single p.natDegree]
    · rw [hahnSeries_coeff_algebra_smul, (hahnSeries_pow_order_of_order_neg_one h1 ho _).2, mul_one]
      rfl
    · intro i hi hne
      have hlt : i < p.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
      have hlt' : (i : ℚ) < p.natDegree := by exact_mod_cast hlt
      rw [hahnSeries_coeff_algebra_smul, HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
      rw [(hahnSeries_pow_order_of_order_neg_one h1 ho i).1]
      linarith
    · intro hn
      exact absurd (Finset.self_mem_range_succ _) hn
  rw [hz, HahnSeries.coeff_zero] at hc
  exact hp0 (Polynomial.leadingCoeff_eq_zero.mp hc.symm)

end GlobalTheory.KZ
