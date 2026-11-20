import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulHerbrandPhiNatCastTotallyRamified
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.Ram.card_mul_herbrandPhi_natCast_of_totallyRamified` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCardMulHerbrandPhiNatCastTotallyRamified.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.card_mul_herbrandPhi_natCast_totallyRamified : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L], lowerRamificationGroup F L 0 = ⊤ → ∀ a : ℕ, (Nat.card (L ≃ₐ[F] L) : ℝ) * herbrandPhi F L a = ((∑ t ∈ Finset.range a, Nat.card ↥(wild F L t) : ℕ) : ℝ) := by
  first | exact @GlobalTheory.PMon.Ram.card_mul_herbrandPhi_natCast_of_totallyRamified | exact GlobalTheory.PMon.Ram.card_mul_herbrandPhi_natCast_of_totallyRamified | (intros; apply GlobalTheory.PMon.Ram.card_mul_herbrandPhi_natCast_of_totallyRamified <;> assumption)
