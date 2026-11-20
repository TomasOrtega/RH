import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsHeatSwd
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FIsHeatSwd.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.isHeat_swd_of_adm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → ∀ (M R : ℕ) (φ : Fam E n N), admitted M R φ → IsHeat Ψ (swd Ψ M φ) := by
  first | exact @GlobalTheory.SW.isHeat_swd | exact GlobalTheory.SW.isHeat_swd | (intros; apply GlobalTheory.SW.isHeat_swd <;> assumption)
