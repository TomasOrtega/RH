import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianLocalRingFixedFieldInertia
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.henselianLocalRing_fixedField_inertia` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHenselianLocalRingFixedFieldInertia.lean&line=219#L219)
-/
theorem _root_.GlobalTheory.T.henselianLocalRing_fixedField_inertia_alt : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → HenselianLocalRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  first | exact @GlobalTheory.henselianLocalRing_fixedField_inertia | exact GlobalTheory.henselianLocalRing_fixedField_inertia | (intros; apply GlobalTheory.henselianLocalRing_fixedField_inertia <;> assumption)
