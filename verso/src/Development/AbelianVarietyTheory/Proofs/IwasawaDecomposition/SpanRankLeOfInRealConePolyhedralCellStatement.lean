import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRankLeOfInRealConePolyhedralCell
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PolFan.genRank_le_of_inRCone_cell` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FSpanRankLeOfInRealConePolyhedralCell.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.spanRank_le_of_inRealCone_polyhedralCell : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m n : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : Fin n → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → (∀ j, v j ∈ balForms bar X) → (∀ j y, 0 ≤ v j y y) → (∀ j, InRCone γ (v j)) → genRank v ≤ genRank γ := by
  first | exact @GlobalTheory.PolFan.genRank_le_of_inRCone_cell | exact GlobalTheory.PolFan.genRank_le_of_inRCone_cell | (intros; apply GlobalTheory.PolFan.genRank_le_of_inRCone_cell <;> assumption)
