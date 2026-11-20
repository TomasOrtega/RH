import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PowEqPowIffModEqOfIsPrimitiveRoot

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld.RayExp

variable {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero, GlobalTheory.NT.Model.heckeIdeal_top]`. Consider the case `succ n ih => rw [pow_succ, pow_succ, GlobalTheory.NT.Model.heckeIdeal_mul L χ (pow_ne_zero n hI) hI, ih]`.
-/
theorem heckeIdeal_pow (χ : (L ≃ₐ[K] L) →* ℂˣ) {I : Ideal (𝓞 K)} (hI : I ≠ 0) (n : ℕ) :
    heckeIdeal L χ (I ^ n) = heckeIdeal L χ I ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, GlobalTheory.NT.Model.heckeIdeal_top]
  | succ n ih => rw [pow_succ, pow_succ, GlobalTheory.NT.Model.heckeIdeal_mul L χ (pow_ne_zero n hI) hI, ih]

/- English proof (translation)
Proceed by induction on `I using UniqueFactorizationMonoid.induction_on_prime with`. Consider the case `h₁ => exact absurd rfl hI`. Consider the case `h₂ x hx => rw [isUnit_iff_eq_one.1 hx, GlobalTheory.NT.Model.heckeIdeal_top, one_pow]`. Consider the case `h₃ a p ha hpp ih`. Set `𝔭 : HeightOneSpectrum (𝓞 K)` to `⟨p, Ideal.isPrime_of_prime hpp, hpp.ne_zero⟩`.

Establish `hnd : ¬ 𝔭.asIdeal ∣ 𝔮` using `fun hd => hpp.not_unit (hc.of_mul_left_left.isUnit_of_dvd' dvd_rfl hd)`. Take `⟨σ, hσ⟩` from `GlobalTheory.NT.exists_isFrob L 𝔭`. Rewrite using `[GlobalTheory.NT.Model.heckeIdeal_mul L _ hpp.ne_zero ha, mul_pow, ih ha hc.of_mul_left_right, mul_one, show p = 𝔭.asIdeal from rfl, GlobalTheory.NT.Model.heckeIdeal_prime, heckeVal_of_unramIn L χ (hun 𝔭 hnd) hσ, ← Units.val_pow_eq_pow_val, ← map_pow, ← IsGalois.card_aut_eq_finra …`.
-/
theorem heckeIdeal_pow_finrank [IsGalois K L] (χ : (L ≃ₐ[K] L) →* ℂˣ) {𝔮 : Ideal (𝓞 K)}
    (hun : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 → UnramIn L 𝔭) (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hc : IsCoprime I 𝔮) : heckeIdeal L χ I ^ Module.finrank K L = 1 := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ x hx => rw [isUnit_iff_eq_one.1 hx, GlobalTheory.NT.Model.heckeIdeal_top, one_pow]
  | h₃ a p ha hpp ih =>
    let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨p, Ideal.isPrime_of_prime hpp, hpp.ne_zero⟩
    have hnd : ¬ 𝔭.asIdeal ∣ 𝔮 := fun hd =>
      hpp.not_unit (hc.of_mul_left_left.isUnit_of_dvd' dvd_rfl hd)
    obtain ⟨σ, hσ⟩ := GlobalTheory.NT.exists_isFrob L 𝔭
    rw [GlobalTheory.NT.Model.heckeIdeal_mul L _ hpp.ne_zero ha, mul_pow, ih ha hc.of_mul_left_right, mul_one,
      show p = 𝔭.asIdeal from rfl, GlobalTheory.NT.Model.heckeIdeal_prime, heckeVal_of_unramIn L χ (hun 𝔭 hnd) hσ,
      ← Units.val_pow_eq_pow_val, ← map_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', map_one,
      Units.val_one]

/- English proof (translation)
Introduce `K L _ _ _ _ _ 𝔮 ⟨hab, hun, _, hart⟩ I hI hc`. Establish `hI0 : I ≠ 0` using `hI`. Use `(hart _ (pow_ne_zero _ hI0) hc.pow_left).1 fun χ => ?_` and prove the remaining obligations. Rewrite using `[heckeIdeal_pow L χ hI0, heckeIdeal_pow_finrank L χ hun I hI0 hc]`.
-/
theorem pow_finrank_principal : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔮 : Ideal (𝓞 K)), IsRayField K L 𝔮 → ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 →
      ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I ^ Module.finrank K L * Ideal.span {β} = Ideal.span {α} := by
  intro K L _ _ _ _ _ 𝔮 ⟨hab, hun, _, hart⟩ I hI hc
  have hI0 : I ≠ 0 := hI
  refine (hart _ (pow_ne_zero _ hI0) hc.pow_left).1 fun χ => ?_
  rw [heckeIdeal_pow L χ hI0, heckeIdeal_pow_finrank L χ hun I hI0 hc]

end GlobalTheory.Mem.Fld.RayExp
