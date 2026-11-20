import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodMapLevelCoverWeightZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalCoeffF
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LvCover.exists_goodMap_rankZero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsGoodMapLevelCoverWeightZero.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_good_map_level_cover_weight_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), D.p + D.q = 0 →
    ∀ (l l' : Level H) (Xo : Moduli D l) (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (h : c'.F ≤ c.F)
      (Y : GlobalTheory.TorRef.GMod Xo c) (Y' : GlobalTheory.TorRef.GMod Xo' c'), ∃ r, GlobalTheory.LvCover.GoodMap h Y Y' r := by
  first | exact @GlobalTheory.LvCover.exists_goodMap_rankZero | exact GlobalTheory.LvCover.exists_goodMap_rankZero | (intros; apply GlobalTheory.LvCover.exists_goodMap_rankZero <;> assumption)
