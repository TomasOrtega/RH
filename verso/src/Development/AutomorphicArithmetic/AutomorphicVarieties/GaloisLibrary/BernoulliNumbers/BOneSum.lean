import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

open Finset UpperTheory.V.Bern

/- English proof (translation)
Use `Finset.sum_nbij' (fun a : ℕ => (a : ZMod N)) (fun b => (b - 1).val + 1) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a _`. Simplify using the standard rewrite rules. Introduce `b _`. Simplify using `only [Finset.mem_Icc]`.

Conclude with `⟨by omega, ZMod.val_lt _⟩`. Introduce `a ha`. Simplify using `only [Finset.mem_Icc] at ha`. Take `⟨k, rfl⟩ : ∃ k, a = k + 1` from `⟨a - 1, by omega⟩`. Establish `hk : k < N` using `by omega`.

Simplify using `[Nat.cast_add, ZMod.val_cast_of_lt hk]`. Introduce `b _`. Use `push_cast`. Simplify using the standard rewrite rules. Introduce `a _`.

Both sides reduce to the same expression.
-/
private theorem UpperTheory.V.Bern.b_one_sum {R : Type} [AddCommMonoid R] {N : ℕ} [NeZero N] (Φ : ZMod N → R) :
    ∑ a ∈ Icc 1 N, Φ (a : ZMod N) = ∑ a : ZMod N, Φ a := by
  refine Finset.sum_nbij' (fun a : ℕ => (a : ZMod N)) (fun b => (b - 1).val + 1) ?_ ?_ ?_ ?_ ?_
  · intro a _
    simp
  · intro b _
    simp only [Finset.mem_Icc]
    exact ⟨by omega, ZMod.val_lt _⟩
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
    have hk : k < N := by omega
    simp [Nat.cast_add, ZMod.val_cast_of_lt hk]
  · intro b _
    push_cast
    simp
  · intro a _
    rfl

/- English proof (translation)
Introduce `R _ _ N _ Φ hΦ`. Simplify using `only [genB, bcoef, Polynomial.bernoulli_one]`. Establish `hs : ∑ a ∈ Icc 1 N, Φ (a : ZMod N) = 0` using `(UpperTheory.V.Bern.b_one_sum Φ).trans hΦ`. Establish `hN : (N : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr (NeZero.ne N)`. Establish `key : ∀ x : ℕ, (N : R) * (Φ (x : ZMod N) * algebraMap ℚ R ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹))) = Φ (x : ZMod N) * (x : R) - algebraMap ℚ R ((N : ℚ) / 2) * Φ (x : ZMod N)`.

Introduce `x`. Establish `e : (N : ℚ) * ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹)) = (x : ℚ) - (N : ℚ) / 2`. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[map_mul (algebraMap ℚ R) (N : ℚ), map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by`. Rewrite using `[e, map_sub, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.mul_sum]`. Repeatedly rewrite using `[key]`. Rewrite using `[Finset.sum_sub_distrib, ← Finset.mul_sum, hs, mul_zero, sub_zero]`.
-/
theorem UpperTheory.V.Bern.b_one :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} [NeZero N] (Φ : ZMod N → R), ∑ a : ZMod N, Φ a = 0 → (N : R) * genB 1 Φ = ∑ a ∈ Icc 1 N, Φ (a : ZMod N) * (a : R) := by
  intro R _ _ N _ Φ hΦ
  simp only [genB, bcoef, Polynomial.bernoulli_one]
  have hs : ∑ a ∈ Icc 1 N, Φ (a : ZMod N) = 0 := (UpperTheory.V.Bern.b_one_sum Φ).trans hΦ
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have key : ∀ x : ℕ, (N : R) * (Φ (x : ZMod N) * algebraMap ℚ R ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹))) = Φ (x : ZMod N) * (x : R) - algebraMap ℚ R ((N : ℚ) / 2) * Φ (x : ZMod N) := by
    intro x
    have e : (N : ℚ) * ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹)) = (x : ℚ) - (N : ℚ) / 2 := by
      simp
      field_simp
    calc (N : R) * (Φ (x : ZMod N) * algebraMap ℚ R ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹)))
        = Φ (x : ZMod N) * algebraMap ℚ R ((N : ℚ) * ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹))) := by
          rw [map_mul (algebraMap ℚ R) (N : ℚ), map_natCast]
          ring
      _ = _ := by
          rw [e, map_sub, map_natCast]
          ring
  rw [Finset.mul_sum]
  simp_rw [key]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs, mul_zero, sub_zero]
