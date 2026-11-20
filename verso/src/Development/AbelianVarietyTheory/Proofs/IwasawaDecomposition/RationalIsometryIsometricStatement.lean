import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalIsometryIsometric
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsom
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.HermIsom Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HermIsom.isometric_of_ratIsom` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FRationalIsometryIsometric.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.rational_isometry_isometric : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (L M : HermLB p), RatIsom L M → L.Isometric M := by
  first | exact @GlobalTheory.HermIsom.isometric_of_ratIsom | exact GlobalTheory.HermIsom.isometric_of_ratIsom | (intros; apply GlobalTheory.HermIsom.isometric_of_ratIsom <;> assumption)
