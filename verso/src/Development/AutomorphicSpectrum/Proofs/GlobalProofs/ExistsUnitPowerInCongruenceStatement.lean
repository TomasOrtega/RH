import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsUnitPowerInCongruence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FExistsUnitPowerInCongruence.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_unit_power_in_congruence : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ → ∃ e : ℕ, 0 < e ∧ ∀ u : (𝓞 F)ˣ, u ^ e ∈ congUnits 𝔣 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.exists_pow_mem_congUnits | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.exists_pow_mem_congUnits | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.exists_pow_mem_congUnits <;> assumption)
