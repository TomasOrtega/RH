import Mathlib
open scoped NNReal TensorProduct

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem powerSeries_pow_eq_expand_zmod (p : ℕ) [hp : Fact p.Prime] (g : PowerSeries (ZMod p)) :
    g ^ p = PowerSeries.expand p hp.out.ne_zero g := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod p) (f := g) p hp.out.ne_zero
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem powerSeries_eq_sum_X_pow_mul_pow (p : ℕ) [hp : Fact p.Prime] (F : PowerSeries (ZMod p)) :
    ∃ G : Fin p → PowerSeries (ZMod p),
      F = ∑ j : Fin p, PowerSeries.X ^ (j : ℕ) * G j ^ p := by
  have hp0 : 0 < p := hp.out.pos
  refine ⟨fun j => PowerSeries.mk fun i => PowerSeries.coeff (p * i + j) F, ?_⟩
  ext n
  rw [map_sum]
  simp_rw [powerSeries_pow_eq_expand_zmod, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_expand]
  rw [Finset.sum_eq_single (⟨n % p, Nat.mod_lt n hp0⟩ : Fin p)]
  · have h1 : n % p ≤ n := Nat.mod_le n p
    have h2 : p ∣ n - n % p := Nat.dvd_sub_mod n
    simp only [h1, h2, if_true, PowerSeries.coeff_mk]
    congr 1
    rw [Nat.mul_div_cancel' h2, Nat.sub_add_cancel h1]
  · intro j _ hj
    split_ifs with h1 h2
    · exfalso
      apply hj
      ext
      simp only
      have hj' : (j : ℕ) < p := j.2
      obtain ⟨c, hc⟩ := h2
      have : n = p * c + j := by omega
      rw [this, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hj']
    · rfl
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem laurentSeries_eq_sum_single_mul_pow :
    ∀ (p : ℕ) [Fact p.Prime] (f : LaurentSeries (ZMod p)), ∃ g : Fin p → LaurentSeries (ZMod p),
      f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ZMod p) * g j ^ p := by
  intro p hp f
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  set N : ℕ := f.order.natAbs with hN
  set m : ℕ := (f.order + p * N).toNat with hm
  have hm' : ((m : ℕ) : ℤ) = f.order + p * N := by
    rw [hm, Int.toNat_of_nonneg]
    have : (f.order.natAbs : ℤ) = |f.order| := Int.natCast_natAbs _
    rw [hN, this]
    have h2 : -f.order ≤ |f.order| := neg_le_abs _
    have h3 : 0 ≤ |f.order| := abs_nonneg _
    nlinarith
  obtain ⟨G, hG⟩ := powerSeries_eq_sum_X_pow_mul_pow p (PowerSeries.X ^ m * f.powerSeriesPart)
  refine ⟨fun j => HahnSeries.single (-(N : ℤ)) (1 : ZMod p) * HahnSeries.ofPowerSeries ℤ _ (G j), ?_⟩
  have key : f = HahnSeries.single (-(p * N : ℤ)) (1 : ZMod p) *
      HahnSeries.ofPowerSeries ℤ _ (PowerSeries.X ^ m * f.powerSeriesPart) := by
    conv_lhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart f]
    rw [map_mul, HahnSeries.ofPowerSeries_X_pow, ← mul_assoc, HahnSeries.single_mul_single, hm',
      mul_one]
    congr 2
    ring
  rw [key, hG, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  rw [map_mul, HahnSeries.ofPowerSeries_X_pow, map_pow, mul_pow, HahnSeries.single_pow, one_pow]
  have : (p • (-(N : ℤ))) = -(p * N : ℤ) := by rw [nsmul_eq_mul]; ring
  rw [this]
  ring

end GlobalTheory
