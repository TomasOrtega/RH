import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.RayFacts

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem rayRel_mono_powMod_anti (F : Type) [Field F] [NumberField F] :
    (∀ 𝔣 𝔣' I J : Ideal (𝓞 F), 𝔣' ≤ 𝔣 → RayRel F 𝔣' I J → RayRel F 𝔣 I J) ∧
    (∀ l n m : ℕ, n ≤ m → powMod F l m ≤ powMod F l n) := by
  refine ⟨?_, ?_⟩
  · rintro 𝔣 𝔣' I J hle ⟨a, b, ha, hb, ha1, hb1, hσ, h⟩
    exact ⟨a, b, ha, hb, hle ha1, hle hb1, hσ, h⟩
  · intro l n m hnm
    exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hnm)

end GlobalTheory.CompanionTheory.RayFacts
