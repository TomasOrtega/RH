import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendLineBundleFactorial
import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_lineBundle_extension_of_isDomain` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExtendLineBundleFactorial.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.extend_line_bundle_factorial : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X] [CompactSpace X] (j : Y ⟶ X), IsOpenImmersion j → (∀ x : X, IsDomain (X.presheaf.stalk x)) → (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ L : LB Y, L.IsLB → ∃ L' : LB X, L'.IsLB ∧ LBIso (L'.pull j) L := by
  first | exact @GlobalTheory.exists_lineBundle_extension_of_isDomain | exact GlobalTheory.exists_lineBundle_extension_of_isDomain | (intros; apply GlobalTheory.exists_lineBundle_extension_of_isDomain <;> assumption)
