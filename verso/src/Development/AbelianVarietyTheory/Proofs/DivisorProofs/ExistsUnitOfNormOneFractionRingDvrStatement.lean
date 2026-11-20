import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfNormOneFractionRingDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KeyEven.fractionRing_norm_one_unit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsUnitOfNormOneFractionRingDvr.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_unit_of_norm_one_fractionRing_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (C : Type) [NormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ a : FractionRing V, ‖algebraMap (FractionRing V) C a‖ = 1 → ∃ u : Vˣ, a = algebraMap V (FractionRing V) u := by
  first | exact @GlobalTheory.KeyEven.fractionRing_norm_one_unit | exact GlobalTheory.KeyEven.fractionRing_norm_one_unit | (intros; apply GlobalTheory.KeyEven.fractionRing_norm_one_unit <;> assumption)
