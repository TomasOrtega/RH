import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBundleBirigidSymmetric
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.canon_isBiRig` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCanonicalFamilyBundleBirigidSymmetric.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.canonicalFamily_bundle_birigid_symmetric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → IsBiRig G P := by
  first | exact @GlobalTheory.Mum.canon_isBiRig | exact GlobalTheory.Mum.canon_isBiRig | (intros; apply GlobalTheory.Mum.canon_isBiRig <;> assumption)
