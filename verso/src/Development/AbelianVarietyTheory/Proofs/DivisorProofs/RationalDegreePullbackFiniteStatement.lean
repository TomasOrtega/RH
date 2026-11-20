import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreePullbackFinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRationalDegreePullbackFinite.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.rational_degree_pullback_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (ν : Y ⟶ X) [IsFinite ν], IsProjCurve ℚ (ratFibre p) → IsProjCurve ℚ (ratFibre (ν ≫ p)) → ν (genericPoint Y) = genericPoint X → ∀ L : LB X, L.IsLB → ratDeg (ν ≫ p) (L.pull ν) = (ν.residueDegree (genericPoint Y) : ℤ) * ratDeg p L := by
  first | exact @GlobalTheory.RatFibreDeg.ratDeg_pull | exact GlobalTheory.RatFibreDeg.ratDeg_pull | (intros; apply GlobalTheory.RatFibreDeg.ratDeg_pull <;> assumption)
