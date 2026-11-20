import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassTermEqVolumeMulOrbitalIntegral
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FClassTermEqVolumeMulOrbitalIntegral.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.classTerm_eq_volume_mul_orbitalIntegral : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H), γ ∈ Γ → IsMulCommutative (cent γ) → ∀ (μ : Measure H) [μ.IsHaarMeasure] (dt : Measure (cent γ)) [dt.IsHaarMeasure] (𝓣 : Set (cent γ)), IsFundamentalDomain (Γ.subgroupOf (cent γ)) 𝓣 dt → dt 𝓣 < ⊤ → ∀ (f : H → ℂ) (c : ℂ), Continuous f → HasCompactSupport f → HasOrbInt μ γ dt f c → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 μ → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt Γ μ 𝓕 γ f (dt.real 𝓣 * c) := by
  first | exact @GlobalTheory.ClassUnfold.hasClassInt_of_hasOrbInt | exact GlobalTheory.ClassUnfold.hasClassInt_of_hasOrbInt | (intros; apply GlobalTheory.ClassUnfold.hasClassInt_of_hasOrbInt <;> assumption)
