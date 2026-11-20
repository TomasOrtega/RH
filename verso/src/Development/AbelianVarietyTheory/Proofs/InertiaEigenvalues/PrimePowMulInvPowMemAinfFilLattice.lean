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
Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

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
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
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
