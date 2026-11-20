import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodMapLevelDivides
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalCoeffF
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsGoodMapLevelDivides.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.exists_good_map_level_divides : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ (l l' : Level H), l'.Dvd l → ∀ (Xo : Moduli D l) (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (h : c'.F ≤ c.F)
      (Y : GlobalTheory.TorRef.GMod Xo c) (Y' : GlobalTheory.TorRef.GMod Xo' c'), ∃ r, GlobalTheory.LvCover.GoodMap h Y Y' r := by
  first | exact @GlobalTheory.LvCover.exists_goodMap_of_dvd | exact GlobalTheory.LvCover.exists_goodMap_of_dvd | (intros; apply GlobalTheory.LvCover.exists_goodMap_of_dvd <;> assumption)
