import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingPreservingTransportOfRankZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DetLine.RankZero.hasTransport_of_rank_zero` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHasMarkingPreservingTransportOfRankZero.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.hasMarkingPreservingTransport_of_rank_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (e : c.F →+* ℂ), D.p + D.q = 0 → HasTransport Xo c U e := by
  first | exact @GlobalTheory.DetLine.RankZero.hasTransport_of_rank_zero | exact GlobalTheory.DetLine.RankZero.hasTransport_of_rank_zero | (intros; apply GlobalTheory.DetLine.RankZero.hasTransport_of_rank_zero <;> assumption)
