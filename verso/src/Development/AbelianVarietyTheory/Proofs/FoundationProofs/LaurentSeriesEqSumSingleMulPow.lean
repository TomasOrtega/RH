import Mathlib
open scoped NNReal TensorProduct

namespace GlobalTheory

/- English proof (translation)
Establish `h` using `MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod p) (f := g) p hp.out.ne_zero`. Rewrite `h` using `[ZMod.frobenius_zmod, MvPowerSeries.map_id]`. Conclude with `h.symm`.
-/
theorem powerSeries_pow_eq_expand_zmod (p : ℕ) [hp : Fact p.Prime] (g : PowerSeries (ZMod p)) :
    g ^ p = PowerSeries.expand p hp.out.ne_zero g := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod p) (f := g) p hp.out.ne_zero
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm

/- English proof (translation)
Establish `hp0 : 0 < p` using `hp.out.pos`. Use `⟨fun j => PowerSeries.mk fun i => PowerSeries.coeff (p * i + j) F, ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Rewrite using `[map_sum]`. Repeatedly rewrite using `[powerSeries_pow_eq_expand_zmod, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_expand]`.

Rewrite using `[Finset.sum_eq_single (⟨n % p, Nat.mod_lt n hp0⟩ : Fin p)]`. Establish `h1 : n % p ≤ n` using `Nat.mod_le n p`. Establish `h2 : p ∣ n - n % p` using `Nat.dvd_sub_mod n`. Simplify using `only [h1, h2, if_true, PowerSeries.coeff_mk]`. Use `congr 1`.

Rewrite using `[Nat.mul_div_cancel' h2, Nat.sub_add_cancel h1]`. Introduce `j _ hj split_ifs with h1 h2`. It suffices to derive a contradiction. Apply `hj` to reduce the goal to its premises. Use `ext`.

Simplify using `only`. Establish `hj' : (j : ℕ) < p` using `j.2`. Take `⟨c, hc⟩` from `h2`. Establish `: n = p * c + j` using `by omega`. Rewrite using `[this, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hj']`.

Both sides reduce to the same expression. Both sides reduce to the same expression. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
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
Introduce `p hp f`. Establish `hp1 : (1 : ℤ) ≤ p` using `by exact_mod_cast hp.out.one_lt.le`. Use `set N : ℕ := f.order.natAbs with hN`. Use `set m : ℕ := (f.order + p * N).toNat with hm`. Establish `hm' : ((m : ℕ) : ℤ) = f.order + p * N`.

Rewrite using `[hm, Int.toNat_of_nonneg]`. Establish `: (f.order.natAbs : ℤ) = |f.order|` using `Int.natCast_natAbs _`. Rewrite using `[hN, this]`. Establish `h2 : -f.order ≤ |f.order|` using `neg_le_abs _`. Establish `h3 : 0 ≤ |f.order|` using `abs_nonneg _`.

Use the polynomial consequences of the given equalities and inequalities. Take `⟨G, hG⟩` from `powerSeries_eq_sum_X_pow_mul_pow p (PowerSeries.X ^ m * f.powerSeriesPart)`. Use `⟨fun j => HahnSeries.single (-(N : ℤ)) (1 : ZMod p) * HahnSeries.ofPowerSeries ℤ _ (G j), ?_⟩` and prove the remaining obligations. Establish `key : f = HahnSeries.single (-(p * N : ℤ)) (1 : ZMod p) * HahnSeries.ofPowerSeries ℤ _ (PowerSeries.X ^ m * f.powerSeriesPart)` using `by conv_lhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart f]`. Rewrite using `[map_mul, HahnSeries.ofPowerSeries_X_pow, ← mul_assoc, HahnSeries.single_mul_single, hm', mul_one]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, hG, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[map_mul, HahnSeries.ofPowerSeries_X_pow, map_pow, mul_pow, HahnSeries.single_pow, one_pow]`. Establish `: (p • (-(N : ℤ))) = -(p * N : ℤ)` using `by rw [nsmul_eq_mul]; ring`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
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
