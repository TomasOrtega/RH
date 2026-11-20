import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisedFibrewiseNonvanishingSection
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.thetaNZ_of_preU` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPreUniformisedFibrewiseNonvanishingSection.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.preUniformised_fibrewise_nonvanishing_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → GlobalTheory.LN.ThetaNZ G U.P.L.L := by
  first | exact @GlobalTheory.Mum.thetaNZ_of_preU | exact GlobalTheory.Mum.thetaNZ_of_preU | (intros; apply GlobalTheory.Mum.thetaNZ_of_preU <;> assumption)
