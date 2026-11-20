import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AutBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQ0

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private not_both regInf_iff regInf_iff_real from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AutBridge
open UpperTheory.GalN.V
open NumberField GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af
/- English proof (translation)
Introduce `_ F Ω _ _ _ _ l _ ι n r`. Establish `hC : ∀ [IsTotallyComplex F], IsAut ι r ↔ ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ AttC ι r π`. Introduce `hF`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨sat, inf, ⟨_, π, rfl, rfl⟩ | ⟨h, -⟩, hr, ha⟩`.

Conclude with `⟨π, (regInf_iff π).1 hr, ha⟩`. Conclude with `(not_both F h hF).elim`. Introduce and unpack `⟨π, hr, ha⟩`. Conclude with `⟨_, _, Or.inl ⟨hF, π, rfl, rfl⟩, (regInf_iff π).2 hr, ha⟩`. Use `⟨?_, hC, ?_⟩` and prove the remaining obligations.

Introduce `hF`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨sat, inf, ⟨h, -⟩ | ⟨_, π, rfl, rfl⟩, hr, ha⟩`. Conclude with `(not_both F hF h).elim`. Conclude with `⟨π, (regInf_iff_real π).1 hr, ha⟩`.

Introduce and unpack `⟨π, hr, ha⟩`. Conclude with `⟨_, _, Or.inr ⟨hF, π, rfl, rfl⟩, (regInf_iff_real π).2 hr, ha⟩`. Introduce `_ h0`. Take `⟨π, hr, -, ha⟩` from `_root_.UpperTheory.GalN.V.autCsd0_of_isAutCsdA h0`. Conclude with `hC.2 ⟨π, hr, ha⟩`.
-/
theorem UpperTheory.GalN.V.automorphy_bridge_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Af.AutBridgeAlt := by
  intro _ F Ω _ _ _ _ l _ ι n r
  have hC : ∀ [IsTotallyComplex F], IsAut ι r ↔ ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ AttC ι r π := by
    intro hF
    constructor
    · rintro ⟨sat, inf, ⟨_, π, rfl, rfl⟩ | ⟨h, -⟩, hr, ha⟩
      · exact ⟨π, (regInf_iff π).1 hr, ha⟩
      · exact (not_both F h hF).elim
    · rintro ⟨π, hr, ha⟩
      exact ⟨_, _, Or.inl ⟨hF, π, rfl, rfl⟩, (regInf_iff π).2 hr, ha⟩
  refine ⟨?_, hC, ?_⟩
  · intro hF
    constructor
    · rintro ⟨sat, inf, ⟨h, -⟩ | ⟨_, π, rfl, rfl⟩, hr, ha⟩
      · exact (not_both F hF h).elim
      · exact ⟨π, (regInf_iff_real π).1 hr, ha⟩
    · rintro ⟨π, hr, ha⟩
      exact ⟨_, _, Or.inr ⟨hF, π, rfl, rfl⟩, (regInf_iff_real π).2 hr, ha⟩
  · intro _ h0
    obtain ⟨π, hr, -, ha⟩ := _root_.UpperTheory.GalN.V.autCsd0_of_isAutCsdA h0
    exact hC.2 ⟨π, hr, ha⟩
end
