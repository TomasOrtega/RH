import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDefiniteHermitianOfFourMulLt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SW.siegel_weil_definite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FSiegelWeilDefiniteHermitianOfFourMulLt.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.siegelWeil_definiteHermitian_of_four_mul_lt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → SWAt Ψ n N := by
  first | exact @GlobalTheory.SW.siegel_weil_definite | exact GlobalTheory.SW.siegel_weil_definite | (intros; apply GlobalTheory.SW.siegel_weil_definite <;> assumption)
