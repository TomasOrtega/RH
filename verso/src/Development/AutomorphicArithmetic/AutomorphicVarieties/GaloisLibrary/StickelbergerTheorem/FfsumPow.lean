import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
import Mathlib.FieldTheory.Finite.Basic

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

/- English proof (translation)
Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Separate the alternatives or extract the components of the hypothesis. Use linear arithmetic over natural numbers and integers. Expand and normalize the polynomial expressions, which then agree. Use the polynomial consequences of the given equalities and inequalities. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem ffsum_pow (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : n < 2 * (p - 1)) :
    ∑ x : ZMod p, x ^ n = if n = p - 1 then -1 else 0 := by
  classical
  have hp2 := hp.out.two_le
  rcases lt_or_ge n (p - 1) with h | h
  · rw [if_neg h.ne]
    have := FiniteField.sum_pow_lt_card_sub_one (ZMod p) n (by rw [ZMod.card]; exact h)
    exact this
  · have hn0 : n ≠ 0 := by omega
    let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x => x, Units.val_injective⟩
    have hmap : Finset.univ.map φ = Finset.univ \ {0} := by
      ext x
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_sdiff,
        Finset.mem_singleton, φ, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨u, rfl⟩
        exact u.ne_zero
      · intro hx
        exact ⟨Units.mk0 x hx, rfl⟩
    have hs : ∑ x : ZMod p, x ^ n = ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ n := by
      rw [← Finset.sum_sdiff (Finset.subset_univ ({0} : Finset (ZMod p))), Finset.sum_singleton,
        zero_pow hn0, add_zero, ← hmap, Finset.sum_map]
      rfl
    rw [hs, FiniteField.sum_pow_units, ZMod.card]
    have hiff : p - 1 ∣ n ↔ n = p - 1 := by
      constructor
      · rintro ⟨c, rfl⟩
        rcases c with _ | _ | c
        · omega
        · ring
        · nlinarith
      · rintro rfl
        exact dvd_refl _
    simp only [hiff]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. It suffices to derive a contradiction. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Use linear arithmetic over natural numbers and integers. Rewrite the indicated hypotheses using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Stick.ffsum :
    ∀ (p : ℕ) [Fact p.Prime] (i j : ℕ), 0 < i → i < p - 1 → 0 < j → j < p - 1 →
    (∑ x : ZMod p, x ^ i * (1 - x) ^ j = 0 ↔ i + j < p - 1) := by
  intro p hp i j hi0 hip hj0 hjp
  have hpp : p.Prime := hp.out
  have key : ∑ x : ZMod p, x ^ i * (1 - x) ^ j =
      ∑ m ∈ Finset.range (j + 1), (-1) ^ m * (j.choose m : ZMod p) * ∑ x : ZMod p, x ^ (i + m) := by
    have h1 : ∀ x : ZMod p, (1 - x) ^ j =
        ∑ m ∈ Finset.range (j + 1), (-x) ^ m * 1 ^ (j - m) * (j.choose m : ZMod p) := by
      intro x
      rw [← add_pow, neg_add_eq_sub]
    simp_rw [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun x _ => ?_
    rw [neg_pow, one_pow, pow_add]
    ring
  have key2 : ∑ m ∈ Finset.range (j + 1), (-1) ^ m * (j.choose m : ZMod p) * ∑ x : ZMod p, x ^ (i + m) =
      ∑ m ∈ Finset.range (j + 1),
        if p - 1 - i = m then -((-1) ^ m * (j.choose m : ZMod p)) else 0 := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [ffsum_pow p (i + m) (by omega)]
    by_cases h : i + m = p - 1
    · rw [if_pos h, if_pos (by omega)]
      ring
    · rw [if_neg h, if_neg (by omega), mul_zero]
  rw [key, key2, Finset.sum_ite_eq]
  split_ifs with h
  · rw [Finset.mem_range] at h
    constructor
    · intro h0
      exfalso
      have hc : (j.choose (p - 1 - i) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        have hdf : p ∣ j.factorial := by
          rw [← Nat.choose_mul_factorial_mul_factorial (show p - 1 - i ≤ j by omega), mul_assoc]
          exact Dvd.dvd.mul_right hd _
        have := (Nat.Prime.dvd_factorial hpp).mp hdf
        omega
      have hu : ((-1 : ZMod p) ^ (p - 1 - i)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
      exact mul_ne_zero hu hc (neg_eq_zero.mp h0)
    · intro h'
      omega
  · rw [Finset.mem_range] at h
    constructor
    · intro _
      omega
    · intro _
      rfl
