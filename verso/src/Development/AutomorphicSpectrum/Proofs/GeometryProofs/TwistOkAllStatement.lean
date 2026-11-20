import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistOkAll
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.TwistOk.twOK_obj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FTwistOkAll.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.twist_ok_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (g : HostAut H) (a : TwIso D g), TwOK o g a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwistOk.twOK_obj | exact GlobalTheory.CompanionTheory.Ar.TwistOk.twOK_obj | (intros; apply GlobalTheory.CompanionTheory.Ar.TwistOk.twOK_obj <;> assumption)
