import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUnitCoeffMulSeriesLeNorm
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FExistsUnitCoeffMulSeriesLeNorm.lean&line=312#L312)
-/
theorem _root_.GlobalTheory.T.exists_unit_coeff_mul_series_le_norm : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (β : ℂ) (N : ℕ), M.Chart ℓ → β ≠ 0 → (∀ l ∈ M.L.lattice, β * l ∈ M.L.lattice) → (N : ℂ) = β * conj β → Bd 1 (hat M.ι ℓ (fun z => M.u (β * z))) → ∃ n ≤ N, ‖coeff n (hat M.ι ℓ (fun z => M.u (β * z)))‖ = 1 := by
  first | exact @GlobalTheory.MomOne.MulDegree.exists_unit_coeff | exact GlobalTheory.MomOne.MulDegree.exists_unit_coeff | (intros; apply GlobalTheory.MomOne.MulDegree.exists_unit_coeff <;> assumption)
