import Mathlib

open Matrix

namespace GlobalTheory

def transvectionUnit {R : Type} [CommRing R] {r : ℕ} {i j : Fin r} (h : i ≠ j) : GL (Fin r) R :=
  ⟨transvection i j (1 : R), transvection i j (-1 : R),
    by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem transvectionUnit_pow_val {R : Type} [CommRing R] {r : ℕ} {i j : Fin r} (h : i ≠ j)
    (n : ℕ) :
    ((transvectionUnit (R := R) h ^ n : GL (Fin r) R) : Matrix (Fin r) (Fin r) R)
      = transvection i j (n : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih]
    change transvection i j (n : R) * transvection i j (1 : R) = _
    rw [transvection_mul_transvection_same _ _ h]
    simp

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem orderOf_transvectionUnit {R : Type} [CommRing R] (q : ℕ) [CharP R q] {r : ℕ}
    {i j : Fin r} (h : i ≠ j) : orderOf (transvectionUnit (R := R) h) = q := by
  have key : ∀ n : ℕ, orderOf (transvectionUnit (R := R) h) ∣ n ↔ q ∣ n := by
    intro n
    rw [orderOf_dvd_iff_pow_eq_one, ← CharP.cast_eq_zero_iff R q n, Units.ext_iff,
      transvectionUnit_pow_val, Units.val_one]
    constructor
    · intro hn
      have := congrFun (congrFun hn i) j
      simpa [transvection, one_apply_ne h] using this
    · intro hn
      rw [hn, transvection_zero]
  exact Nat.dvd_antisymm ((key q).2 dvd_rfl) ((key _).1 dvd_rfl)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem two_mul_pow_four_dvd_card_generalLinearGroup :
    ∀ (R : Type) [CommRing R] [Finite R] (p : ℕ), Odd p → CharP R (p ^ 4) → 1 < p →
      ∀ r : ℕ, 2 ≤ r → 2 * p ^ 4 ∣ Nat.card (GL (Fin r) R) := by
  intro R _ _ p hp hchar h1 r hr
  have hij : (⟨0, by omega⟩ : Fin r) ≠ ⟨1, by omega⟩ := by simp
  have hq : p ^ 4 ∣ Nat.card (GL (Fin r) R) := by
    rw [← orderOf_transvectionUnit (R := R) (p ^ 4) hij]
    exact orderOf_dvd_natCard _
  have h2 : (2 : R) ≠ 0 := by
    intro h
    have hd : p ^ 4 ∣ 2 := (CharP.cast_eq_zero_iff R (p ^ 4) 2).1 (by exact_mod_cast h)
    have hle := Nat.le_of_dvd (by norm_num) hd
    have : 2 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left h1 4
    omega
  have hneg : orderOf (-1 : GL (Fin r) R) = 2 := by
    apply orderOf_eq_prime
    · simp
    · intro h
      have h' := congrArg (fun u : GL (Fin r) R =>
        (u : Matrix (Fin r) (Fin r) R) ⟨0, by omega⟩ ⟨0, by omega⟩) h
      simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at h'
      apply h2
      linear_combination -h'
  have h2d : 2 ∣ Nat.card (GL (Fin r) R) := by
    rw [← hneg]
    exact orderOf_dvd_natCard _
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
    (Nat.Coprime.pow_right 4 ((Nat.coprime_two_left).2 hp)) h2d hq

end GlobalTheory
