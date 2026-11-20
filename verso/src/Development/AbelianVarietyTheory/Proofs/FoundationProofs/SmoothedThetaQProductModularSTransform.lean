import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaProductSiegelModularSTransformStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductEqOddThetaProductQuotientStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaProductSiegelEqZeroIffLatticeStatement
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory

open GlobalTheory.Sieg

/- English proof (translation)
Unfold `ee`. Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma Sieg.cthS_ee_pow (w : ℂ) (n : ℕ) : ee w ^ n = ee ((n : ℂ) * w) := by
  unfold ee
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/- English proof (translation)
Establish `h2 : Nat.Coprime c 2` using `Nat.Coprime.coprime_dvd_right (by norm_num) hc`. Establish `hodd : Odd c`. Break down `Nat.even_or_odd c with h | h` into its components or cases. It suffices to derive a contradiction. Take `⟨j, hj⟩` from `h`.

Establish `: 2 ∣ Nat.gcd c 2` using `Nat.dvd_gcd ⟨j, by omega⟩ dvd_rfl`. Rewrite `this` using `[h2]`. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Take `⟨j, rfl⟩` from `hodd`.

Establish `: (2 * j + 1) ^ 2 = 4 * (j ^ 2 + j) + 1` using `by ring`. Rewrite using `[this, pow_succ, pow_mul]`. Establish `h4 : (-Complex.I) ^ 4 = 1`. Rewrite using `[show (4 : ℕ) = 2 * 2 from rfl, pow_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[h4, one_pow, one_mul]`.
-/
lemma Sieg.cthS_negI_pow (c : ℕ) (hc : Nat.Coprime c 6) : (-Complex.I) ^ (c ^ 2) = -Complex.I := by
  have h2 : Nat.Coprime c 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hc
  have hodd : Odd c := by
    rcases Nat.even_or_odd c with h | h
    · exfalso
      obtain ⟨j, hj⟩ := h
      have : 2 ∣ Nat.gcd c 2 := Nat.dvd_gcd ⟨j, by omega⟩ dvd_rfl
      rw [h2] at this
      omega
    · exact h
  obtain ⟨j, rfl⟩ := hodd
  have : (2 * j + 1) ^ 2 = 4 * (j ^ 2 + j) + 1 := by ring
  rw [this, pow_succ, pow_mul]
  have h4 : (-Complex.I) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    simp
  rw [h4, one_pow, one_mul]

/- English proof (translation)
Establish `hτ : (τ : ℂ) ≠ 0` using `τ.ne_zero`. Establish `hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -(τ : ℂ)⁻¹`. Rewrite using `[UpperHalfPlane.modular_S_smul]`. Simplify using `[inv_neg]`. Establish `hB : th ((c : ℂ) * z) τ ≠ 0`.

Introduce `h`. Take `⟨m, n, hmn⟩` from `(GlobalTheory.T.oddThetaProductSiegel_eq_zero_iff_lattice τ _).1 h`. Conclude with `hz m n hmn`. Establish `hB' : th ((c : ℂ) * (z / (τ : ℂ))) (ModularGroup.S • τ) ≠ 0`. Introduce `h`.

Take `⟨m, n, hmn⟩` from `(GlobalTheory.T.oddThetaProductSiegel_eq_zero_iff_lattice _ _).1 h`. Rewrite `hmn` using `[hS]`. Apply `hz n (-m)` to reduce the goal to its premises. Establish `: (c : ℂ) * z = (τ : ℂ) * ((c : ℂ) * (z / (τ : ℂ)))` using `by field_simp`. Rewrite using `[this, hmn]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[GlobalTheory.T.smoothedThetaQProduct_eq_oddThetaProduct_quotient c _ _ h1 hc hB', GlobalTheory.T.smoothedThetaQProduct_eq_oddThetaProduct_quotient c _ _ h1 hc hB]`. Rewrite using `[show (c : ℂ) * (z / (τ : ℂ)) = ((c : ℂ) * z) / (τ : ℂ) by ring]`.

Rewrite using `[GlobalTheory.T.oddThetaProductSiegel_modularS_transform τ z, GlobalTheory.T.oddThetaProductSiegel_modularS_transform τ ((c : ℂ) * z)]`. Establish `hee : ee (z ^ 2 / (2 * (τ : ℂ))) ^ (c ^ 2) = ee (((c : ℂ) * z) ^ 2 / (2 * (τ : ℂ)))`. Rewrite using `[Sieg.cthS_ee_pow]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hE : ee (((c : ℂ) * z) ^ 2 / (2 * (τ : ℂ))) ≠ 0` using `Complex.exp_ne_zero _`. Establish `hI : (-Complex.I) ≠ 0` using `by simp`. Rewrite using `[mul_pow, mul_pow, Sieg.cthS_negI_pow c hc, hee]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[mul_comm, mul_div_assoc, div_self (by unfold ee; exact Complex.exp_ne_zero _), mul_one]`.
-/
theorem Sieg.cth_modular_S (c : ℕ) (τ : ℍ) (z : ℂ) (h1 : 1 < c) (hc : Nat.Coprime c 6)
    (hz : ∀ m n : ℤ, (c : ℂ) * z ≠ (m : ℂ) * (τ : ℂ) + n) :
    cth c (ee ((ModularGroup.S • τ : ℍ) : ℂ)) (ee (z / (τ : ℂ))) = cth c (ee (τ : ℂ)) (ee z) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -(τ : ℂ)⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [inv_neg]

  have hB : th ((c : ℂ) * z) τ ≠ 0 := by
    intro h
    obtain ⟨m, n, hmn⟩ := (GlobalTheory.T.oddThetaProductSiegel_eq_zero_iff_lattice τ _).1 h
    exact hz m n hmn

  have hB' : th ((c : ℂ) * (z / (τ : ℂ))) (ModularGroup.S • τ) ≠ 0 := by
    intro h
    obtain ⟨m, n, hmn⟩ := (GlobalTheory.T.oddThetaProductSiegel_eq_zero_iff_lattice _ _).1 h
    rw [hS] at hmn
    apply hz n (-m)
    have : (c : ℂ) * z = (τ : ℂ) * ((c : ℂ) * (z / (τ : ℂ))) := by field_simp
    rw [this, hmn]
    push_cast
    field_simp
    ring
  rw [GlobalTheory.T.smoothedThetaQProduct_eq_oddThetaProduct_quotient c _ _ h1 hc hB', GlobalTheory.T.smoothedThetaQProduct_eq_oddThetaProduct_quotient c _ _ h1 hc hB]
  rw [show (c : ℂ) * (z / (τ : ℂ)) = ((c : ℂ) * z) / (τ : ℂ) by ring]
  rw [GlobalTheory.T.oddThetaProductSiegel_modularS_transform τ z, GlobalTheory.T.oddThetaProductSiegel_modularS_transform τ ((c : ℂ) * z)]
  have hee : ee (z ^ 2 / (2 * (τ : ℂ))) ^ (c ^ 2) = ee (((c : ℂ) * z) ^ 2 / (2 * (τ : ℂ))) := by
    rw [Sieg.cthS_ee_pow]
    congr 1
    push_cast
    ring
  have hE : ee (((c : ℂ) * z) ^ 2 / (2 * (τ : ℂ))) ≠ 0 := Complex.exp_ne_zero _
  have hI : (-Complex.I) ≠ 0 := by simp
  rw [mul_pow, mul_pow, Sieg.cthS_negI_pow c hc, hee]
  field_simp
  rw [mul_comm, mul_div_assoc, div_self (by unfold ee; exact Complex.exp_ne_zero _), mul_one]

end GlobalTheory
