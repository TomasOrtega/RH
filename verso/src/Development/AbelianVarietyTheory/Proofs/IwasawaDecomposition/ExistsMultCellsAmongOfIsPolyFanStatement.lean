import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultCellsAmongOfIsPolyFan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PolFan.CellClass.multCellsAmong_of_isPolyFan` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsMultCellsAmongOfIsPolyFan.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.exists_multCellsAmong_of_isPolyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ : InvFun (𝓞 E)),
    IsPolyFan H.bar q φ → ∀ M : ℕ, ∃ n : ℕ, MultCellsAmong H.bar q φ M n := by
  first | exact @GlobalTheory.PolFan.CellClass.multCellsAmong_of_isPolyFan | exact GlobalTheory.PolFan.CellClass.multCellsAmong_of_isPolyFan | (intros; apply GlobalTheory.PolFan.CellClass.multCellsAmong_of_isPolyFan <;> assumption)
