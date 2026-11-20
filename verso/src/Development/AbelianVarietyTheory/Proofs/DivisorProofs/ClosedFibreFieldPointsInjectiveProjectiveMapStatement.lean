import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreFieldPointsInjectiveProjectiveMap
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.ClosedFibreInj.closedFibre_inj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FClosedFibreFieldPointsInjectiveProjectiveMap.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.closedFibre_fieldPoints_injective_projective_map : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (a a' : Sp Ω ⟶ N.U.left), a ≫ N.U.hom = spMap (κ.comp (residue R)) → a' ≫ N.U.hom = spMap (κ.comp (residue R)) → a ≫ fU = a' ≫ fU → a = a' := by
  first | exact @GlobalTheory.Mum.ClosedFibreInj.closedFibre_inj | exact GlobalTheory.Mum.ClosedFibreInj.closedFibre_inj | (intros; apply GlobalTheory.Mum.ClosedFibreInj.closedFibre_inj <;> assumption)
