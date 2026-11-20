import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHarishChandraParamOfTypeOfUnitaryW
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.besType_hcParam` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FExistsHarishChandraParamOfTypeOfUnitaryW.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.exists_harishChandraParam_of_typeOfUnitaryW : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → Q.IsType k r z π u → ∃ u₀, PI.UpqRep.IsHCTypeW k r z u₀ π := by
  first | exact @GlobalTheory.besType_hcParam | exact GlobalTheory.besType_hcParam | (intros; apply GlobalTheory.besType_hcParam <;> assumption)
