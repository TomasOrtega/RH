import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumPolarisedAbelianLocalDomain
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MBLow.exists_keyIn_local` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsKeyDatumPolarisedAbelianLocalDomain.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.exists_keyDatum_polarisedAbelian_localDomain : ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (P : PolAV (Sp W)), 1 ≤ P.g → ∃ y : KeyIn W, y.P = P := by
  first | exact @GlobalTheory.MBLow.exists_keyIn_local | exact GlobalTheory.MBLow.exists_keyIn_local | (intros; apply GlobalTheory.MBLow.exists_keyIn_local <;> assumption)
