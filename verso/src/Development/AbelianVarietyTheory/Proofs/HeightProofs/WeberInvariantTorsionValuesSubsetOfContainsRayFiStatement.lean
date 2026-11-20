import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetOfContainsRayFi
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FWeberInvariantTorsionValuesSubsetOfContainsRayFi.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.weberInvariantTorsionValues_subset_of_containsRayField : ∀ (K L : IntermediateField ℚ ℂ) [NumberField K] [NumberField L] [IsTotallyComplex K] (h : K ≤ L), Module.finrank ℚ K = 2 → discr K < -4 → ∀ P : PeriodPair, (∀ z, z ∈ P.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, 3 ≤ n → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (IntermediateField.inclusion h).toRingHom n → weberSet P n ⊆ L := by
  first | exact @GlobalTheory.FieldSize.WeberIn.weberSet_subset | exact GlobalTheory.FieldSize.WeberIn.weberSet_subset | (intros; apply GlobalTheory.FieldSize.WeberIn.weberSet_subset <;> assumption)
