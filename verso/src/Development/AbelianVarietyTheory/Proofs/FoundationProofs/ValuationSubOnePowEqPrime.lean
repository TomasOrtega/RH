import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

/- English proof (translation)
Rewrite using `[← mul_neg_geom_sum, v.map_mul]`. Establish `hs : v (∑ i ∈ Finset.range n, η ^ i) ≤ 1`. Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[v.map_pow]`.

Conclude with `pow_le_one₀ (zero_le') hη`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem valuation_one_sub_pow_le {L : Type} [Field L] (v : Valuation L ℝ≥0) (η : L)
    (hη : v η ≤ 1) (n : ℕ) : v (1 - η ^ n) ≤ v (1 - η) := by
  rw [← mul_neg_geom_sum, v.map_mul]
  have hs : v (∑ i ∈ Finset.range n, η ^ i) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [v.map_pow]
    exact pow_le_one₀ (zero_le') hη
  calc v (1 - η) * v (∑ i ∈ Finset.range n, η ^ i) ≤ v (1 - η) * 1 := by gcongr
    _ = v (1 - η) := mul_one _

/- English proof (translation)
Introduce `L _ v p hp ζ hζ`. Establish `hone : ∀ η : L, η ^ p = 1 → v η ≤ 1`. Introduce `η hη`. Establish `h1 : v η ^ p = 1` using `by rw [← v.map_pow, hη, v.map_one]`. Conclude with `le_of_eq ((pow_eq_one_iff_of_nonneg (zero_le') hp.ne_zero).mp h1)`.

Take `⟨n, rfl⟩ : ∃ n, p = n + 1` from `⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩`. Establish `hprod` using `hζ.prod_one_sub_pow_eq_order`. Establish `hterm : ∀ k ∈ Finset.range n, v (1 - ζ ^ (k + 1)) = v (ζ - 1)`. Introduce `k hk`. Rewrite `hk` using `[Finset.mem_range]`.

Rewrite using `[Valuation.map_sub_swap v ζ 1]`. Establish `hc : (k + 1).Coprime (n + 1)`. Establish `h` using `Nat.coprime_of_lt_prime (Nat.succ_ne_zero k) (by omega : k + 1 < n + 1) hp`. Apply the tactic sequence `first | exact h | exact h.symm`. Establish `hprim : IsPrimitiveRoot (ζ ^ (k + 1)) (n + 1)` using `hζ.pow_of_coprime _ hc`.

Apply `le_antisymm` to reduce the goal to its premises. Conclude with `valuation_one_sub_pow_le v ζ (hone ζ hζ.pow_eq_one) (k + 1)`. Take `⟨i, -, hi⟩` from `hprim.eq_pow_of_pow_eq_one hζ.pow_eq_one`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, ← hprod, map_prod, Finset.prod_congr rfl hterm, Finset.prod_const, Finset.card_range]`.
-/
theorem valuation_sub_one_pow_eq_prime :
    ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ ζ : L,
      IsPrimitiveRoot ζ p → v (ζ - 1) ^ (p - 1) = v (p : L) := by
  intro L _ v p hp ζ hζ
  have hone : ∀ η : L, η ^ p = 1 → v η ≤ 1 := by
    intro η hη
    have h1 : v η ^ p = 1 := by rw [← v.map_pow, hη, v.map_one]
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (zero_le') hp.ne_zero).mp h1)
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  have hprod := hζ.prod_one_sub_pow_eq_order
  have hterm : ∀ k ∈ Finset.range n, v (1 - ζ ^ (k + 1)) = v (ζ - 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Valuation.map_sub_swap v ζ 1]
    have hc : (k + 1).Coprime (n + 1) := by
      have h := Nat.coprime_of_lt_prime (Nat.succ_ne_zero k) (by omega : k + 1 < n + 1) hp
      first | exact h | exact h.symm
    have hprim : IsPrimitiveRoot (ζ ^ (k + 1)) (n + 1) := hζ.pow_of_coprime _ hc
    apply le_antisymm
    · exact valuation_one_sub_pow_le v ζ (hone ζ hζ.pow_eq_one) (k + 1)
    · obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hζ.pow_eq_one
      calc v (1 - ζ) = v (1 - (ζ ^ (k + 1)) ^ i) := by rw [hi]
        _ ≤ v (1 - ζ ^ (k + 1)) :=
          valuation_one_sub_pow_le v _ (hone _ hprim.pow_eq_one) i
  rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, ← hprod, map_prod, Finset.prod_congr rfl hterm, Finset.prod_const,
    Finset.card_range]

end GlobalTheory.AlmostEt
