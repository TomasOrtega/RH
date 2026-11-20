import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPTorsionIntegralAndDistinctMod
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FWeierstrassPTorsionIntegralAndDistinctMod.lean&line=243#L243)
-/
theorem _root_.GlobalTheory.T.weierstrassP_torsion_integral_and_distinct_mod : ∀ (L : PeriodPair) (W : ValuationSubring ℂ) (m : ℕ), (2 : ℂ)⁻¹ ∈ W → (3 : ℂ)⁻¹ ∈ W → L.g₂ ∈ W → L.g₃ ∈ W → (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W → Odd m → (m : ℂ)⁻¹ ∈ W → (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP t ∈ W) ∧ ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice → t' ∉ L.lattice → L.weierstrassP t - L.weierstrassP t' ∈ W.nonunits → t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice := by
  first | exact @GlobalTheory.TorsionIntegral.torsion_integral_distinct | exact GlobalTheory.TorsionIntegral.torsion_integral_distinct | (intros; apply GlobalTheory.TorsionIntegral.torsion_integral_distinct <;> assumption)
