import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalSymmetricStructureOfGenericSymmetri
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCubicalSymmetricStructureOfGenericSymmetri.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.exists_cubicalSymmetricStructure_of_genericSymmetric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R], ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → IsProper (pullback.snd G.hom (jK R)) → ∀ L : LB G.left, L.IsLB → Out.Sym ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) → ∃ P : GlobalTheory.UU.CP G, P.L.L = L := by
  first | exact @GlobalTheory.CubSymPkg.exists_cp_of_generic_sym | exact GlobalTheory.CubSymPkg.exists_cp_of_generic_sym | (intros; apply GlobalTheory.CubSymPkg.exists_cp_of_generic_sym <;> assumption)
