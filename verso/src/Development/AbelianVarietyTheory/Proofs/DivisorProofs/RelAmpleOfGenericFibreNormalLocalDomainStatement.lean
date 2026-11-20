import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfGenericFibreNormalLocalDomain
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRelAmpleOfGenericFibreNormalLocalDomain.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.relAmple_of_genericFibre_normalLocalDomain : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap (algebraMap O K)) φ → ∀ (M : LB A.left) (M' : LB A'.left), M.IsLB → M'.IsLB → LBIso M' (M.pull φ) → Out.RelAmple A' M' → Out.RelAmple A M := by
  first | exact @GlobalTheory.AmpleGenericLocal.relAmple_of_generic | exact GlobalTheory.AmpleGenericLocal.relAmple_of_generic | (intros; apply GlobalTheory.AmpleGenericLocal.relAmple_of_generic <;> assumption)
