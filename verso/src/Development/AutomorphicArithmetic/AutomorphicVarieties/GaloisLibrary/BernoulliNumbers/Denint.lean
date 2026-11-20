import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Expand
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primden

open Finset UpperTheory.V.Bern

/- English proof (translation)
Introduce `N k a hN`. It suffices to establish `h : (den N k : ℚ) * bcoef N k a ∈ (Int.castRingHom ℚ).range by`. Take `⟨z, hz⟩` from `h`. Conclude with `⟨z, hz.symm⟩`. Rewrite using `[b_expand N k a hN, Finset.mul_sum]`.

Use `Subring.sum_mem _ fun j hj => ?_` and prove the remaining obligations. Establish `hjk : j ≤ k` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)`. Take `⟨z, hz⟩` from `b_primden k j hjk`. Establish `hN' : (N : ℚ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hpow : (N : ℚ) * (N : ℚ) ^ ((j : ℤ) - 1) = (N : ℚ) ^ j`.

Rewrite using `[← zpow_one_add₀ hN', add_sub_cancel, zpow_natCast]`. Use `⟨(k.choose j : ℤ) * z * (N : ℤ) ^ j * (a : ℤ) ^ (k - j), ?_⟩` and prove the remaining obligations. Unfold `den`. Rewrite using `[eq_intCast]`. Use `push_cast`.

Rewrite using `[← hz, ← hpow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Bern.b_denint :
    ∀ (N k a : ℕ), 0 < N → ∃ z : ℤ, (den N k : ℚ) * bcoef N k a = z := by
  intro N k a hN
  suffices h : (den N k : ℚ) * bcoef N k a ∈ (Int.castRingHom ℚ).range by
    obtain ⟨z, hz⟩ := h
    exact ⟨z, hz.symm⟩
  rw [b_expand N k a hN, Finset.mul_sum]
  refine Subring.sum_mem _ fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  obtain ⟨z, hz⟩ := b_primden k j hjk
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpow : (N : ℚ) * (N : ℚ) ^ ((j : ℤ) - 1) = (N : ℚ) ^ j := by
    rw [← zpow_one_add₀ hN', add_sub_cancel, zpow_natCast]
  refine ⟨(k.choose j : ℤ) * z * (N : ℤ) ^ j * (a : ℤ) ^ (k - j), ?_⟩
  unfold den
  rw [eq_intCast]
  push_cast
  rw [← hz, ← hpow]
  ring
