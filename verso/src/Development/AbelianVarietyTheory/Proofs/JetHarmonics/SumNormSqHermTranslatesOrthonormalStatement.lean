import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormSqHermTranslatesOrthonormal
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FSumNormSqHermTranslatesOrthonormal.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.sum_norm_sq_herm_translates_orthonormal : ∀ (k r : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : Mx k r → Matrix ι ι ℂ) (Γ U : Matrix ι ι ℂ) (d : ℕ) (om : ι → ℂ), IsFRep ρ Γ d → U ∈ Matrix.unitaryGroup ι ℂ → ∀ g ∈ GG k r, ∑ e, ‖Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ (fun c => U e c)) om‖ ^ 2 = ∑ i, ‖(ρ g⁻¹ *ᵥ om) i‖ ^ 2 := by
  first | exact @GlobalTheory.MomentParseval.sum_herm_sq | exact GlobalTheory.MomentParseval.sum_herm_sq | (intros; apply GlobalTheory.MomentParseval.sum_herm_sq <;> assumption)
