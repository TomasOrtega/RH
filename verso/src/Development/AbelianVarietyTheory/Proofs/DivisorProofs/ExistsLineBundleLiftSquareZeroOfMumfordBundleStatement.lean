import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftSquareZeroOfMumfordBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLineBundleLiftSquareZeroOfMumfordBundle.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.exists_lineBundle_lift_squareZero_of_mumfordBundle : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (B : Over (Sp R)) [GrpObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] [IsCommMonObj B₀] (i : B₀.left ⟶ B.left) (i₂ : (G2 B₀).left ⟶ (G2 B).left), IsAbelianScheme B → IsGrpPullback B₀ B (spMap π) i → IsSquare i i₂ → ∀ (P : LB (G2 B).left) (L₀ : LB B₀.left), P.IsLB → L₀.IsLB → LBIso (abelian₂ B₀ L₀) (P.pull i₂) → ∃ L : LB B.left, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  first | exact @GlobalTheory.LBObs.exists_lift_of_lam_iso_pull | exact GlobalTheory.LBObs.exists_lift_of_lam_iso_pull | (intros; apply GlobalTheory.LBObs.exists_lift_of_lam_iso_pull <;> assumption)
