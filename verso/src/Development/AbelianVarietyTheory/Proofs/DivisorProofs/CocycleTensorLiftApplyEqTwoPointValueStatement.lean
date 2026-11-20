import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleTensorLiftApplyEqTwoPointValue
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCocycleTensorLiftApplyEqTwoPointValue.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.cocycle_tensorLift_apply_eq_twoPointValue : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ) (D : Type) [CommRing D] [Algebra R D] (φ ψ : G.A n →ₐ[R] D), Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ Commute.all _ _) (d.coc n) = d.g D (spOver φ ≫ t.y n) (spOver ψ ≫ t.y n) - ((fv d.f (G.A n) D (toConv φ * toConv ψ).ofConv (t.y n) + (toConv φ * toConv ψ).ofConv (d.h n)) - (fv d.f (G.A n) D φ (t.y n) + φ (d.h n)) - (fv d.f (G.A n) D ψ (t.y n) + ψ (d.h n))) := by
  first | exact @GlobalTheory.PtExt.Dat.lift_coc | exact GlobalTheory.PtExt.Dat.lift_coc | (intros; apply GlobalTheory.PtExt.Dat.lift_coc <;> assumption)
