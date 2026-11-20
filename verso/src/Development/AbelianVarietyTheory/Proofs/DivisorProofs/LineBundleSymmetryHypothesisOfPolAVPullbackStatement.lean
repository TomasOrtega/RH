import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisOfPolAVPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Poinc.hypS_polAV_pullback` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLineBundleSymmetryHypothesisOfPolAVPullback.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.lineBundleSymmetryHypothesis_of_polAV_pullback : ∀ {S S' : Scheme.{0}} (P : PolAV S) (P' : PolAV S') (f : S' ⟶ S) (ψ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f ψ → LBIso P'.L (P.L.pull ψ) → HypS P.A P.L → HypS P'.A P'.L := by
  first | exact @GlobalTheory.Poinc.hypS_polAV_pullback | exact GlobalTheory.Poinc.hypS_polAV_pullback | (intros; apply GlobalTheory.Poinc.hypS_polAV_pullback <;> assumption)
