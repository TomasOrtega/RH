import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfDescendsNearClosedFibre
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.descend_of_near` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSemiAbelianDescendsOfDescendsNearClosedFibre.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.semiAbelian_descends_of_descends_near_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), IsSemiAbelian G ∧ IsGrpPullback G' G π β ∧ IsOpenImmersion i.left ∧ N.u ≫ β = pullback.fst _ _ ≫ i.left := by
  first | exact @GlobalTheory.Mum.descend_of_near | exact GlobalTheory.Mum.descend_of_near | (intros; apply GlobalTheory.Mum.descend_of_near <;> assumption)
