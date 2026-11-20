import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFlagUnipotentEqStabilizerTimesSection
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLintegralFlagUnipotentEqStabilizerTimesSection.lean&line=369#L369)
-/
theorem _root_.GlobalTheory.T.lintegral_flagUnipotent_eq_stabilizer_times_section : ∀ (k r j : ℕ) (β : Fin r → ℕ), Monotone β → (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) → ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ n, f n ∂(lebN k r) = ∫⁻ q : PSec k r j × (UToff β → ℂ), ∫⁻ ρ, f (rmulM (sEl k r j β q) ρ) ∂(lebR0 k r j β) := by
  first | exact @GlobalTheory.Amp.RadConj.lebN_split | exact GlobalTheory.Amp.RadConj.lebN_split | (intros; apply GlobalTheory.Amp.RadConj.lebN_split <;> assumption)
