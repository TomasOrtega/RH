import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselZhatInvAndRegularIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FBesselZhatInvAndRegularIff.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.besselZhat_inv_and_regular_iff : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r), γ ∈ GG k r → Zhat k r z' z γ⁻¹ = (Zhat k r z z' γ)ᴴ ∧ (γ ∈ Greg k r z z' ↔ γ⁻¹ ∈ Greg k r z' z) := by
  first | exact @GlobalTheory.SgInf.RegInv.zhat_inv_and_reg | exact GlobalTheory.SgInf.RegInv.zhat_inv_and_reg | (intros; apply GlobalTheory.SgInf.RegInv.zhat_inv_and_reg <;> assumption)
