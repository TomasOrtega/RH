import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreConstOfSpecialisationInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFibreConstOfSpecialisationInvariant.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.fibre_const_of_specialisation_invariant : ∀ (Y Z : Type) [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] [T0Space Z] (q : Y → Z), Continuous q → ∀ z : Z, _root_.IsPreconnected (q ⁻¹' {z}) → ∀ P : Y → Prop, (∀ a b, q a = z → q b = z → a ⤳ b → (P a ↔ P b)) → ∀ a b, q a = z → q b = z → P a → P b := by
  first | exact @GlobalTheory.fibre_const_of_specializes_invariant | exact GlobalTheory.fibre_const_of_specializes_invariant | (intros; apply GlobalTheory.fibre_const_of_specializes_invariant <;> assumption)
