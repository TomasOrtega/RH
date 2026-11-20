import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfInvPiModXiPowBoundedDenominatorStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

/- English proof (translation)
Take `⟨h1, h2⟩` from `hs`. Distinguish the cases in `h : l = 2`. Use `⟨k + 1, by subst h; omega, ?_⟩` and prove the remaining obligations. Use `Nat.mul_le_mul_right k (h2 h)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `h3 : 2 ≤ l - 1` using `by have := hl.two_le; omega`. Use `⟨k / 2 + 1, ?_, ?_⟩` and prove the remaining obligations. Use `Nat.mul_le_mul_right (k / 2 + 1) h3` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `Nat.mul_le_mul_right k h1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_exponent_small {l s : ℕ} (hl : l.Prime) (hs : Lev l s) (M n k : ℕ) (hM : 1 ≤ M)
    (hk : 2 * (M + n) ≤ k) : ∃ N : ℕ, k + 1 ≤ (l - 1) * N ∧ N + M - 1 + n ≤ s * k := by
  obtain ⟨h1, h2⟩ := hs
  by_cases h : l = 2
  · refine ⟨k + 1, by subst h; omega, ?_⟩
    have := Nat.mul_le_mul_right k (h2 h)
    omega
  · have h3 : 2 ≤ l - 1 := by have := hl.two_le; omega
    refine ⟨k / 2 + 1, ?_, ?_⟩
    · have := Nat.mul_le_mul_right (k / 2 + 1) h3
      omega
    · have := Nat.mul_le_mul_right k h1
      omega

/- English proof (translation)
Use `⟨2 * (M + n), fun k hk a => ?_⟩` and prove the remaining obligations. Establish `hu' : u ^ (k + 1) ∈ FilB P 0` using `by simpa using FilB_pow hu (k + 1)`. Break down `Nat.eq_zero_or_pos M with rfl | hM` into its components or cases. Apply `FilB_le_Lat` to reduce the goal to its premises. Use `FilB_zero_mul (io_mem AI (((l : ℕ) : Ainf l) ^ (s * k) * a)) hu'` as an intermediate fact.

Simplify `this` using `only [map_mul, map_pow, map_natCast, Nat.cast_zero]`. Take `⟨N, hN1, hN2⟩` from `exists_exponent_small (Fact.out : l.Prime) hs M n k hM hk`. Take `⟨a', b', hab⟩` from `Ideal.mem_span_pair.mp (GlobalTheory.T.ainf_invPi_mod_xi_pow_bounded_denominator l P AI (k + 1) N M hM hN1)`. Take `⟨e, he⟩` from `Nat.exists_eq_add_of_le hN2`. Establish `hio` using `congrArg (io AI) hab`.

Simplify using `only [map_mul, map_pow, map_natCast, map_add] at hio`. Establish `hxk : io AI AI.π₁ ^ (k + 1) * u ^ (k + 1) = 1` using `by rw [← mul_pow, hx, one_pow]`. Establish `hξ : io AI AI.ξ ^ M ∈ FilB P (M : ℤ)` using `by simpa using FilB_pow (io_ξ_mem AI) M`. Use `⟨((l : ℕ) : Ainf l) ^ e * a * a', ?_⟩` and prove the remaining obligations. Use `FilB_zero_mul (FilB_zero_mul (io_mem AI (((l : ℕ) : Ainf l) ^ n * ((l : ℕ) : Ainf l) ^ e * a * b')) hu') hξ` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[he, pow_add, pow_add _ (N + M - 1), ← hio]`. Simplify using `only [map_mul, map_pow, map_natCast]`. Take the linear combination `((l : P.R.BdR) ^ n * (l : P.R.BdR) ^ e * io AI a * io AI a') * hxk`.
-/
theorem pow_mul_inv_pow_mem_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (s : ℕ)
    (hs : Lev l s) (u : P.R.BdR) (hu : u ∈ FilB P 0) (hx : io AI AI.π₁ * u = 1) (M n : ℕ) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ a : Ainf l,
      (l : P.R.BdR) ^ (s * k) * io AI a * u ^ (k + 1) ∈ Lat AI M n := by
  refine ⟨2 * (M + n), fun k hk a => ?_⟩
  have hu' : u ^ (k + 1) ∈ FilB P 0 := by simpa using FilB_pow hu (k + 1)
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · apply FilB_le_Lat
    have := FilB_zero_mul (io_mem AI (((l : ℕ) : Ainf l) ^ (s * k) * a)) hu'
    simpa only [map_mul, map_pow, map_natCast, Nat.cast_zero] using this
  obtain ⟨N, hN1, hN2⟩ := exists_exponent_small (Fact.out : l.Prime) hs M n k hM hk
  obtain ⟨a', b', hab⟩ := Ideal.mem_span_pair.mp (GlobalTheory.T.ainf_invPi_mod_xi_pow_bounded_denominator l P AI (k + 1) N M hM hN1)
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hN2
  have hio := congrArg (io AI) hab
  simp only [map_mul, map_pow, map_natCast, map_add] at hio
  have hxk : io AI AI.π₁ ^ (k + 1) * u ^ (k + 1) = 1 := by rw [← mul_pow, hx, one_pow]
  have hξ : io AI AI.ξ ^ M ∈ FilB P (M : ℤ) := by simpa using FilB_pow (io_ξ_mem AI) M
  refine ⟨((l : ℕ) : Ainf l) ^ e * a * a', ?_⟩
  have := FilB_zero_mul
    (FilB_zero_mul (io_mem AI (((l : ℕ) : Ainf l) ^ n * ((l : ℕ) : Ainf l) ^ e * a * b')) hu') hξ
  convert this using 1
  rw [he, pow_add, pow_add _ (N + M - 1), ← hio]
  simp only [map_mul, map_pow, map_natCast]
  linear_combination ((l : P.R.BdR) ^ n * (l : P.R.BdR) ^ e * io AI a * io AI a') * hxk

end GlobalTheory.ExpImage
