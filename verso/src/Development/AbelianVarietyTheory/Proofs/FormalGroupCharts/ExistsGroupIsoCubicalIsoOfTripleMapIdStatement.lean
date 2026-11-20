import Mathlib
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGroupIsoCubicalIsoOfTripleMapId
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ChartCmp.exists_iso_of_sabMap_id` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFormalGroupCharts%2FExistsGroupIsoCubicalIsoOfTripleMapId.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.exists_groupIso_cubicalIso_of_tripleMap_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))), ∃ ψ : t.G ≅ t'.G, ψ.hom.left = n.φ ∧ IsMonHom ψ.hom ∧ (∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a) ∧ n.cm.F3 = (ψ.hom ⊗ₘ ψ.hom ⊗ₘ ψ.hom).left ∧ ∃ w : LB.Iso t.PP.L (t'.PP.L.pull n.φ), CubIso n w := by
  first | exact @GlobalTheory.ChartCmp.exists_iso_of_sabMap_id | exact GlobalTheory.ChartCmp.exists_iso_of_sabMap_id | (intros; apply GlobalTheory.ChartCmp.exists_iso_of_sabMap_id <;> assumption)
