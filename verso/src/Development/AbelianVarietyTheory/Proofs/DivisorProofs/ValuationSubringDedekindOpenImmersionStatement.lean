import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringDedekindOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FValuationSubringDedekindOpenImmersion.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.valuation_subring_dedekind_open_immersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (W : ValuationSubring c.F), GlobalTheory.Models.IsDedFrac W.subtype ∧ IsOpenImmersion (spMap W.subtype) := by
  first | exact @GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion | exact GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion | (intros; apply GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion <;> assumption)
