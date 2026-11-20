import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemePower
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CM.exists_polAV_isPowGrp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCubicalLineBundles%2FExistsPolarisedAbelianSchemePower.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.exists_polarisedAbelianScheme_power : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (n : ℕ), ∃ (Q : Out.PolAV (Sp R)) (_ : Out.IsPowGrp Q.A P.A n), Q.g = n * P.g := by
  first | exact @GlobalTheory.CM.exists_polAV_isPowGrp | exact GlobalTheory.CM.exists_polAV_isPowGrp | (intros; apply GlobalTheory.CM.exists_polAV_isPowGrp <;> assumption)
