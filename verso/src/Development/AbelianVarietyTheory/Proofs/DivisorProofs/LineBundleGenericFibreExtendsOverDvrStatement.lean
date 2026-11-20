import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGenericFibreExtendsOverDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.lb_extends_over_dvr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLineBundleGenericFibreExtendsOverDvr.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.lineBundle_generic_fibre_extends_over_dvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (H : Over (Sp R)) [Smooth H.hom] [QuasiCompact H.hom] [IsSeparated H.hom] [GeometricallyIntegral H.hom] (L : LB ((Over.pullback (jK R)).obj H).left), L.IsLB → ∃ L' : LB H.left, L'.IsLB ∧ LBIso L (L'.pull (pullback.fst H.hom (jK R))) := by
  first | exact @GlobalTheory.Mum.lb_extends_over_dvr | exact GlobalTheory.Mum.lb_extends_over_dvr | (intros; apply GlobalTheory.Mum.lb_extends_over_dvr <;> assumption)
