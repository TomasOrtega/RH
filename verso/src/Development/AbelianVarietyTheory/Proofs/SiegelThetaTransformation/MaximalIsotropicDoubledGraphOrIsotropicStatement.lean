import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MaximalIsotropicDoubledGraphOrIsotropic
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SW.lag_graph_or_isotropic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FMaximalIsotropicDoubledGraphOrIsotropic.lean&line=101#L101)
-/
theorem _root_.GlobalTheory.T.maximalIsotropic_doubled_graph_or_isotropic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ γ γ' : GL (Fin r) E, IsUn X γ → IsUn X γ' → botSpan (iota X 1 γ) = botSpan (iota X 1 γ') → γ = γ') ∧ ∀ U : Lag E r, (∃ γ : GL (Fin r) E, IsUn X γ ∧ botSpan (iota X 1 γ) = U.1) ∨ ∃ ξ : Fin r → E, ξ ≠ 0 ∧ herm X.Gm ξ ξ = 0 ∧ Sum.elim ξ 0 ᵥ* dblT X ∈ U.1 := by
  first | exact @GlobalTheory.SW.lag_graph_or_isotropic | exact GlobalTheory.SW.lag_graph_or_isotropic | (intros; apply GlobalTheory.SW.lag_graph_or_isotropic <;> assumption)
