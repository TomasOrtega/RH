import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualOfCovolumeOne
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotient
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSelfDualOfCovolumeOne.lean&line=165#L165)
-/
theorem _root_.GlobalTheory.T.selfDual_of_fundamentalDomain_volume_eq_one : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ B : G → G → ℂ, (∀ y, Continuous fun x => B x y) → (∀ x y, B x y = B y x) → (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ x y, ‖B x y‖ = 1) → (∀ x, (∀ γ ∈ Γ, B γ x = 1) ↔ x ∈ Γ) → (∀ γ ∈ Γ, (∀ x, B γ x = 1) → γ = 0) → ∀ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual μ B := by
  first | exact @GlobalTheory.CovolumeOneSelfDual.selfDual_of_covolume_one | exact GlobalTheory.CovolumeOneSelfDual.selfDual_of_covolume_one | (intros; apply GlobalTheory.CovolumeOneSelfDual.selfDual_of_covolume_one <;> assumption)
