import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatRationalCoordsIntegralProportional
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FSchwartzBruhatRationalCoordsIntegralProportional.lean&line=113#L113)
-/
theorem _root_.GlobalTheory.T.schwartzBruhat_rationalCoords_integral_proportional : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → haar (fun m : Matrix (Fin n) (QI E N) ℚ => φ (ofQ m)) = c * haar φ := by
  first | exact @GlobalTheory.SW.haar_ofQ_proportional | exact GlobalTheory.SW.haar_ofQ_proportional | (intros; apply GlobalTheory.SW.haar_ofQ_proportional <;> assumption)
