import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsHeatThH
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SW.isHeat_thH` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FIsHeatThH.lean&line=209#L209)
-/
theorem _root_.GlobalTheory.T.isHeat_thH_of_isSB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (φ : Matrix (Fin n) (Fin N) E → ℂ), IsSB φ → IsHeat Ψ (thH Ψ φ) := by
  first | exact @GlobalTheory.SW.isHeat_thH | exact GlobalTheory.SW.isHeat_thH | (intros; apply GlobalTheory.SW.isHeat_thH <;> assumption)
