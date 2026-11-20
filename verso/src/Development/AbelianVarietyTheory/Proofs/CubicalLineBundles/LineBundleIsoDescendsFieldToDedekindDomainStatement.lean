import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LineBundleIsoDescendsFieldToDedekindDomain
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IsoDescent.lbIso_of_field` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCubicalLineBundles%2FLineBundleIsoDescendsFieldToDedekindDomain.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.lineBundleIso_descends_field_to_dedekindDomain : ∀ (R k : Type) [CommRing R] [IsDedekindDomain R] [Field k] (β : R →+* k), Function.Injective β → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (p : X' ⟶ Sp k), IsPullback π p A.hom (spMap β) → ∀ N N' : LB A.left, N.IsLB → N'.IsLB → LBIso (N.pull (eSec A)) (N'.pull (eSec A)) → LBIso (N.pull π) (N'.pull π) → LBIso N N' := by
  first | exact @GlobalTheory.IsoDescent.lbIso_of_field | exact GlobalTheory.IsoDescent.lbIso_of_field | (intros; apply GlobalTheory.IsoDescent.lbIso_of_field <;> assumption)
