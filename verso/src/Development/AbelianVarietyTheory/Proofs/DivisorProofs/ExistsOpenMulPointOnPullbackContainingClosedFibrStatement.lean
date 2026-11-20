import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenMulPointOnPullbackContainingClosedFibr
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsOpenMulPointOnPullbackContainingClosedFibr.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.exists_open_mul_point_on_pullback_containing_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (N : Near M.π G'), ∃ (O : (pullback (N.U ⊗ N.U).hom M.π).Opens) (h : O.toScheme ⟶ N.U.left), (∀ z : ↥(pullback (N.U ⊗ N.U).hom M.π), (N.U ⊗ N.U).hom (pullback.fst (N.U ⊗ N.U).hom M.π z) = closedPoint R → z ∈ O) ∧ h ≫ N.U.hom = O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (N.U ⊗ N.U).hom ∧ ∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (s : T ⟶ M.S) (x y : Over.mk s ⟶ G'), t ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π = s → N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (fst N.U N.U).left) x.left → N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (snd N.U N.U).left) y.left → N.Pt s (t ≫ h) (x * y).left := by
  first | exact @GlobalTheory.Mum.Near.exists_mul_pt_pullback | exact GlobalTheory.Mum.Near.exists_mul_pt_pullback | (intros; apply GlobalTheory.Mum.Near.exists_mul_pt_pullback <;> assumption)
