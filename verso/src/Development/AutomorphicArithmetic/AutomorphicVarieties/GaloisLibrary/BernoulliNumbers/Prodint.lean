import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Ratprod
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primmem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Denupper
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BNzC
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Parity

open Finset UpperTheory.V.Bern

/- English proof (translation)
Introduce `N _ k P hk hP`. Take `⟨q, hq⟩` from `b_ratprod P (fun Ω _ _ χ => (den N k : Ω) * Bprim k χ) (by`. Introduce `K Ω _ _ _ _ f χ`. Simplify using `only [map_mul, map_natCast]`. Rewrite using `[b_primmap f f.injective])`.

Establish `hfin : (charSet ℂ P).Finite` using `Set.toFinite _`. Use `haveI : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩`. Establish `hC` using `hq ℂ`. Rewrite `hC` using `[finprod_mem_eq_finite_toFinset_prod _ hfin]`. Establish `hint : IsIntegral ℤ (q : ℂ)`.

Rewrite using `[← hC]`. Conclude with `IsIntegral.prod _ fun χ _ => (b_primmem k χ).2.2.1`. Establish `hint' : IsIntegral ℤ q`. Establish `: (q : ℂ) = algebraMap ℚ ℂ q` using `rfl`. Rewrite `hint` using `[this]`.

Conclude with `(isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp hint`. Take `⟨M, hM⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint'`. Establish `hM' : (M : ℚ) = q` using `by simpa using hM`. Substitute `hM'` using the available equality. Establish `hC' : ∏ χ ∈ hfin.toFinset, (den N k : ℂ) * Bprim k χ = (M : ℂ)`.

Rewrite using `[hC]`. Simplify using the standard rewrite rules. Establish `hM0 : M ≠ 0`. Establish `: (M : ℂ) ≠ 0`. Rewrite using `[← hC']`.

Use `Finset.prod_ne_zero_iff.mpr fun χ hχ => mul_ne_zero ?_ ?_` and prove the remaining obligations. Conclude with `Nat.cast_ne_zero.mpr (den_pos (NeZero.pos N) k).ne'`. Establish `hχ' : χ.toUnitHom.ker ∈ P` using `hfin.mem_toFinset.mp hχ`. Conclude with `(b_nzC χ k hk ((b_parity k χ).1.mp (hP hχ'))).1`. Conclude with `this` after adjusting the coercions.

Use `⟨M, hM0, ?_, fun Ω _ _ _ => ?_⟩` and prove the remaining obligations. Establish `hle : |(M : ℝ)| ≤ bnd N k ^ (charSet ℂ P).ncard`. Establish `h1 : |(M : ℝ)| = ‖(M : ℂ)‖` using `by simp`. Rewrite using `[h1, ← hC', norm_prod, Set.ncard_eq_toFinset_card _ hfin, ← Finset.prod_const]`. Conclude with `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun χ _ => (b_denupper k χ).2.1`.

Rewrite using `[← Real.log_pow]`. Conclude with `Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hM0)) hle`. Rewrite using `[hq Ω]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Bern.b_prodint :
    ∀ {N : ℕ} [NeZero N] (k : ℕ) (P : Set (Subgroup (ZMod N)ˣ)), 1 ≤ k → P ⊆ parKer N k → ∃ M : ℤ, M ≠ 0 ∧ Real.log |(M : ℝ)| ≤ (charSet ℂ P).ncard * Real.log (bnd N k) ∧ ∀ (Ω : Type) [Field Ω] [CharZero Ω] [HasEnoughRootsOfUnity Ω (Monoid.exponent (ZMod N)ˣ)], ∏ᶠ χ ∈ charSet Ω P, (den N k : Ω) * Bprim k χ = (M : Ω) := by
  intro N _ k P hk hP
  obtain ⟨q, hq⟩ := b_ratprod P (fun Ω _ _ χ => (den N k : Ω) * Bprim k χ) (by
    intro K Ω _ _ _ _ f χ
    simp only [map_mul, map_natCast]
    rw [b_primmap f f.injective])
  have hfin : (charSet ℂ P).Finite := Set.toFinite _
  haveI : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hC := hq ℂ
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin] at hC
  have hint : IsIntegral ℤ (q : ℂ) := by
    rw [← hC]
    exact IsIntegral.prod _ fun χ _ => (b_primmem k χ).2.2.1
  have hint' : IsIntegral ℤ q := by
    have : (q : ℂ) = algebraMap ℚ ℂ q := rfl
    rw [this] at hint
    exact (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp hint
  obtain ⟨M, hM⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  have hM' : (M : ℚ) = q := by simpa using hM
  subst hM'
  have hC' : ∏ χ ∈ hfin.toFinset, (den N k : ℂ) * Bprim k χ = (M : ℂ) := by
    rw [hC]; simp
  have hM0 : M ≠ 0 := by
    have : (M : ℂ) ≠ 0 := by
      rw [← hC']
      refine Finset.prod_ne_zero_iff.mpr fun χ hχ => mul_ne_zero ?_ ?_
      · exact Nat.cast_ne_zero.mpr (den_pos (NeZero.pos N) k).ne'
      · have hχ' : χ.toUnitHom.ker ∈ P := hfin.mem_toFinset.mp hχ
        exact (b_nzC χ k hk ((b_parity k χ).1.mp (hP hχ'))).1
    exact_mod_cast this
  refine ⟨M, hM0, ?_, fun Ω _ _ _ => ?_⟩
  · have hle : |(M : ℝ)| ≤ bnd N k ^ (charSet ℂ P).ncard := by
      have h1 : |(M : ℝ)| = ‖(M : ℂ)‖ := by simp
      rw [h1, ← hC', norm_prod, Set.ncard_eq_toFinset_card _ hfin, ← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun χ _ => (b_denupper k χ).2.1
    rw [← Real.log_pow]
    exact Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hM0)) hle
  · rw [hq Ω]; simp
