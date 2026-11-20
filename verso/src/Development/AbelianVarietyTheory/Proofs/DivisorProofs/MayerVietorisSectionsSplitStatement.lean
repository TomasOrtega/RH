import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisSectionsSplit
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwoOpens.sections_inter_eq_sub_of_subsingleton_cohOn` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMayerVietorisSectionsSplit.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.mayer_vietoris_sections_split : ∀ (Y : Scheme.{0}) (F : Y.Modules) (W₁ W₂ : Y.Opens), Subsingleton (cohOn F (W₁ ⊔ W₂) 1) → ∀ t : sectionsOn F (W₁ ⊓ W₂), ∃ (a : sectionsOn F W₁) (b : sectionsOn F W₂), t = sectionsOn.res Γ(Y, ⊤) F inf_le_right b - sectionsOn.res Γ(Y, ⊤) F inf_le_left a := by
  first | exact @GlobalTheory.TwoOpens.sections_inter_eq_sub_of_subsingleton_cohOn | exact GlobalTheory.TwoOpens.sections_inter_eq_sub_of_subsingleton_cohOn | (intros; apply GlobalTheory.TwoOpens.sections_inter_eq_sub_of_subsingleton_cohOn <;> assumption)
