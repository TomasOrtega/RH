import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam

/- English proof (translation)
The claim follows from `(ReciprocityTheory.ChartRestriction.L1.jInv_eq_jT h).symm`.
-/
theorem jT_eq_latDisc (Λ : PeriodPair) (c : ℂ) (τ : ℍ) (h : IsTauOf Λ c τ) :
    jT τ = 1728 * Λ.g₂ ^ 3 / latDisc Λ :=
  (ReciprocityTheory.ChartRestriction.L1.jInv_eq_jT h).symm

/- English proof (translation)
Establish `hc : c ≠ 0` using `h.1`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `hI : Complex.I ^ 12 = 1`. Rewrite using `[show (12 : ℕ) = 4 * 3 from rfl, pow_mul, Complex.I_pow_four, one_pow]`. Establish `hd : latDisc Λ = (c ^ 12)⁻¹ * (4096 * (Real.pi : ℂ) ^ 12) * DD τ` using `ReciprocityTheory.ChartRestriction.L1.disc_eq h`.

Rewrite using `[div_pow, mul_pow, mul_pow, mul_pow, hI, hΩ, hd]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pow_twelve_eq_DD (Λ : PeriodPair) (c : ℂ) (τ : ℍ) (h : IsTauOf Λ c τ) (Ω : ℂ)
    (hΩ : Ω ^ 12 = latDisc Λ) : (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ := by
  have hc : c ≠ 0 := h.1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ^ 12 = 1 := by
    rw [show (12 : ℕ) = 4 * 3 from rfl, pow_mul, Complex.I_pow_four, one_pow]
  have hd : latDisc Λ = (c ^ 12)⁻¹ * (4096 * (Real.pi : ℂ) ^ 12) * DD τ :=
    ReciprocityTheory.ChartRestriction.L1.disc_eq h
  rw [div_pow, mul_pow, mul_pow, mul_pow, hI, hΩ, hd]
  field_simp
  ring

/- English proof (translation)
Introduce `Λ c τ h` and use `⟨jT_eq_latDisc Λ c τ h, pow_twelve_eq_DD Λ c τ h⟩`.
-/
theorem jT_eq_and_pow_twelve_eq_DD : ∀ (Λ : PeriodPair) (c : ℂ) (τ : ℍ), IsTauOf Λ c τ → jT τ = 1728 * Λ.g₂ ^ 3 / latDisc Λ ∧ ∀ Ω : ℂ, Ω ^ 12 = latDisc Λ → (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ :=
  fun Λ c τ h => ⟨jT_eq_latDisc Λ c τ h, pow_twelve_eq_DD Λ c τ h⟩

end GlobalTheory.QFam
