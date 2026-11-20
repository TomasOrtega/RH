import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe

open UpperTheory.V UpperTheory.V.PropA

/- English proof (translation)
Introduce `l _ X _ _ w`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `k n H x`. Take `⟨y, hy⟩` from `H x`. Use `⟨(∑ i ∈ Finset.range n, w ^ i) y, ?_⟩` and prove the remaining obligations.

Rewrite using `[← geom_sum_mul, Module.End.mul_apply, hy, map_smul]`. Introduce `H x`. Take `⟨y, hy⟩` from `H x`. Take `⟨y', hy'⟩` from `H y`. Rewrite `hy`, `hy'` using `[pow_one]`.

Use `⟨y + ∑ i ∈ Finset.range l, (∑ j ∈ Finset.range i, w ^ j) y', ?_⟩` and prove the remaining obligations. Establish `hw : ∀ i, (w ^ i) y = y + (l : ℤ_[l]) • (∑ j ∈ Finset.range i, w ^ j) y'`. Introduce `i`. Establish `h0 : (w ^ i - 1) y = (∑ j ∈ Finset.range i, w ^ j) ((w - 1) y)`. Rewrite using `[← Module.End.mul_apply, geom_sum_mul]`.

Rewrite `h0` using `[hy', map_smul]`. Rewrite using `[← h0, LinearMap.sub_apply, Module.End.one_apply, add_sub_cancel]`. Rewrite using `[← geom_sum_mul, Module.End.mul_apply, hy, map_smul, LinearMap.sum_apply]`. Repeatedly rewrite using `[hw]`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.smul_sum, ← Nat.cast_smul_eq_nsmul ℤ_[l], ← smul_add, pow_two, mul_smul]`.
-/
theorem UpperTheory.V.PropA.powIn :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (w : Module.End ℤ_[l] X),
      (∀ k n : ℕ, InPow k (w - 1) → InPow k (w ^ n - 1)) ∧ (InPow 1 (w - 1) → InPow 2 (w ^ l - 1)) := by
  intro l _ X _ _ w
  refine ⟨?_, ?_⟩
  · intro k n H x
    obtain ⟨y, hy⟩ := H x
    refine ⟨(∑ i ∈ Finset.range n, w ^ i) y, ?_⟩
    rw [← geom_sum_mul, Module.End.mul_apply, hy, map_smul]
  · intro H x
    obtain ⟨y, hy⟩ := H x
    obtain ⟨y', hy'⟩ := H y
    rw [pow_one] at hy hy'
    refine ⟨y + ∑ i ∈ Finset.range l, (∑ j ∈ Finset.range i, w ^ j) y', ?_⟩
    have hw : ∀ i, (w ^ i) y = y + (l : ℤ_[l]) • (∑ j ∈ Finset.range i, w ^ j) y' := by
      intro i
      have h0 : (w ^ i - 1) y = (∑ j ∈ Finset.range i, w ^ j) ((w - 1) y) := by
        rw [← Module.End.mul_apply, geom_sum_mul]
      rw [hy', map_smul] at h0
      rw [← h0, LinearMap.sub_apply, Module.End.one_apply, add_sub_cancel]
    rw [← geom_sum_mul, Module.End.mul_apply, hy, map_smul, LinearMap.sum_apply]
    simp_rw [hw]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.smul_sum,
      ← Nat.cast_smul_eq_nsmul ℤ_[l], ← smul_add, pow_two, mul_smul]
