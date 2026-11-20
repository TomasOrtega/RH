import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPrincipallyPolarisedFibreIffOfGrpPullback.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback : ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (A : Over S') [GrpObj A] (L' : LB A.left) (f : S' ⟶ S) (φ : A.left ⟶ G.left), L.IsLB → L'.IsLB → IsGrpPullback A G f φ → LBIso L' (L.pull φ) → ∀ (g : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S'), (PolFib A L' g x ↔ PolFib G L g (x ≫ f)) ∧ ∀ (R' : Type) [CommRing R'] (i : R →+* R'), PolFib A L' g x → PolFib A L' g (spMap i ≫ x) := by
  first | exact @GlobalTheory.UMin.FibMove.polFib_move | exact GlobalTheory.UMin.FibMove.polFib_move | (intros; apply GlobalTheory.UMin.FibMove.polFib_move <;> assumption)
