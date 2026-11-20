import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceDimensionEqSumChoose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFlagSpaceDimensionEqSumChoose.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.flag_space_dimension_eq_sum_choose : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H), Dw.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 = Module.finrank ℚ E / 2 * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) := by
  first | exact @GlobalTheory.FlagDimSum.dim_add_sum_choose | exact GlobalTheory.FlagDimSum.dim_add_sum_choose | (intros; apply GlobalTheory.FlagDimSum.dim_add_sum_choose <;> assumption)
