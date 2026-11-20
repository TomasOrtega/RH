import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilFormulaDegreeSucc
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SW.swAt_succ` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FSiegelWeilFormulaDegreeSucc.lean&line=242#L242)
-/
theorem _root_.GlobalTheory.T.siegelWeil_formula_degree_succ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → SWAt Ψ n (N + 1) := by
  first | exact @GlobalTheory.SW.swAt_succ | exact GlobalTheory.SW.swAt_succ | (intros; apply GlobalTheory.SW.swAt_succ <;> assumption)
