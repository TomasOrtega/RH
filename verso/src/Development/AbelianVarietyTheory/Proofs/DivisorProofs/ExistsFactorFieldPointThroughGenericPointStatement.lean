import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorFieldPointThroughGenericPoint
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.Modif.factor_gp` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFactorFieldPointThroughGenericPoint.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_factor_field_point_through_generic_point : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (L : Type) [Field L] (ρ : R →+* L) (y : Sp L ⟶ M.S), Function.Injective ρ → y ≫ M.π = spMap ρ → ∃ ga : FractionRing R →+* L, (∀ r, ga (algebraMap R _ r) = ρ r) ∧ y = spMap ga ≫ M.gp := by
  first | exact @GlobalTheory.Mum.Modif.factor_gp | exact GlobalTheory.Mum.Modif.factor_gp | (intros; apply GlobalTheory.Mum.Modif.factor_gp <;> assumption)
