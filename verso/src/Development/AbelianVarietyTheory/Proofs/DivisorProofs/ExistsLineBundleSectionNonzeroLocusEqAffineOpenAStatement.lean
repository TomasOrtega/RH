import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSectionNonzeroLocusEqAffineOpenA
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_lineBundle_section_nonzeroLocus_eq_affineOpen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLineBundleSectionNonzeroLocusEqAffineOpenA.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_section_nonzeroLocus_eq_affineOpen : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ M : LB A.left, M.IsLB ∧ ∃ s : LB.Sec M, Out.nonzeroLocus s = V := by
  first | exact @GlobalTheory.exists_lineBundle_section_nonzeroLocus_eq_affineOpen | exact GlobalTheory.exists_lineBundle_section_nonzeroLocus_eq_affineOpen | (intros; apply GlobalTheory.exists_lineBundle_section_nonzeroLocus_eq_affineOpen <;> assumption)
