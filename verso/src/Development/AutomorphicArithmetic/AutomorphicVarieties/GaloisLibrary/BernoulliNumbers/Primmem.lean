import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primval
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Denchar

open Finset UpperTheory.V.Bern

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private theorem dirichletCharacter_unit_isIntegral {R : Type} [CommRing R] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) (u : (ZMod N)ˣ) : IsIntegral ℤ (χ u) := by
  have hpos : 0 < orderOf u := orderOf_pos u
  refine IsIntegral.of_pow hpos ?_
  have h1 : χ (u : ZMod N) ^ orderOf u = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
  rw [h1]
  exact isIntegral_one

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Bern.b_primmem :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter R N), (∀ A : Subalgebra ℚ R, (∀ u : (ZMod N)ˣ, χ u ∈ A) → Bprim k χ ∈ A) ∧ (∀ A : Subring R, (∀ u : (ZMod N)ˣ, χ u ∈ A) → (den N k : R) * Bprim k χ ∈ A) ∧ IsIntegral ℤ ((den N k : R) * Bprim k χ) ∧ IsIntegral ℤ ((den N k : R) * genB k χ) := by
  intro R _ _ N _ k χ
  have hN : N ≠ 0 := NeZero.ne N
  have hc : 0 < χ.conductor :=
    Nat.pos_of_ne_zero fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ χ.conductor_dvd_level))
  have hdvd : den χ.conductor k ∣ den N k := den_dvd χ.conductor_dvd_level k
  have hB : Bprim k χ = genB k (⇑χ.primitiveCharacter) := rfl
  have hint : ∀ a : ZMod N, IsIntegral ℤ (χ a) := by
    intro a
    by_cases ha : IsUnit a
    · obtain ⟨u, rfl⟩ := ha
      exact dirichletCharacter_unit_isIntegral χ u
    · rw [MulChar.map_nonunit χ ha]
      exact isIntegral_zero
  have part2 : ∀ A : Subring R, (∀ u : (ZMod N)ˣ, χ u ∈ A) → (den N k : R) * Bprim k χ ∈ A := by
    intro A hA
    obtain ⟨m, hm⟩ := hdvd
    have hmem : (den χ.conductor k : R) * genB k (⇑χ.primitiveCharacter) ∈ A := by
      refine b_denchar k _ A hc ?_
      intro x
      rcases b_primval χ x with h | ⟨u, h⟩
      · rw [h]; exact A.zero_mem
      · rw [h]; exact hA u
    rw [hB, hm, Nat.cast_mul, mul_comm ((den χ.conductor k : ℕ) : R) (m : R), mul_assoc]
    exact A.mul_mem (natCast_mem A m) hmem
  refine ⟨?_, part2, ?_, ?_⟩
  · intro A hA
    rw [hB]
    refine genB_mem k _ A ?_
    intro x
    rcases b_primval χ x with h | ⟨u, h⟩
    · rw [h]; exact A.zero_mem
    · rw [h]; exact hA u
  · have := part2 (integralClosure ℤ R).toSubring (fun u => dirichletCharacter_unit_isIntegral χ u)
    exact this
  · have := b_denchar k (⇑χ) (integralClosure ℤ R).toSubring (Nat.pos_of_ne_zero hN) (fun a => hint a)
    exact this
