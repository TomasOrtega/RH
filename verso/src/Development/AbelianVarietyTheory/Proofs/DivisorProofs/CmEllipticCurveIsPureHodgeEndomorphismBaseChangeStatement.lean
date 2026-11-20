import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEllipticCurveIsPureHodgeEndomorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureBCId
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PureLift.isPureBC_ell` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCmEllipticCurveIsPureHodgeEndomorphismBaseChange.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.cmEllipticCurve_isPureHodgeEndomorphismBaseChange : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Type) [CommRing S] (ω : S) (C : GlobalTheory.CM.Ell H S ω), IsPureBC C.P.A (C.act.act (GlobalTheory.CM.wK H)) (1 - ω) ω := by
  first | exact @GlobalTheory.PureLift.isPureBC_ell | exact GlobalTheory.PureLift.isPureBC_ell | (intros; apply GlobalTheory.PureLift.isPureBC_ell <;> assumption)
