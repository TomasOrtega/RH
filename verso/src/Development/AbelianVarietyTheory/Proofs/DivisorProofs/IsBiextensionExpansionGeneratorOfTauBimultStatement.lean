import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiextensionExpansionGeneratorOfTauBimult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsBiextensionExpansionGeneratorOfTauBimult.lean&line=313#L313)
-/
theorem _root_.GlobalTheory.T.isBiextensionExpansionGenerator_of_tauBimult : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (K : Type) [Fintype K] (n : K → ℤ) (T : Over (Sp R)) (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A)), Expand D n x y := by
  first | exact @GlobalTheory.Mum.PowData.expand_of_tauBimult | exact GlobalTheory.Mum.PowData.expand_of_tauBimult | (intros; apply GlobalTheory.Mum.PowData.expand_of_tauBimult <;> assumption)
