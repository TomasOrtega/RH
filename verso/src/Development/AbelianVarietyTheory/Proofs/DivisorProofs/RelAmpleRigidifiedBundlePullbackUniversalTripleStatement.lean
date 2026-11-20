import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidifiedBundlePullbackUniversalTriple
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PullAmpleXF.relAmple_XF` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRelAmpleRigidifiedBundlePullbackUniversalTriple.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.relAmple_rigidifiedBundle_pullback_universalTriple : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → RelAmple tF.G tF.PP.L := by
  first | exact @GlobalTheory.PullAmpleXF.relAmple_XF | exact GlobalTheory.PullAmpleXF.relAmple_XF | (intros; apply GlobalTheory.PullAmpleXF.relAmple_XF <;> assumption)
