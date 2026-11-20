import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPrimitiveDeRhamTorsionTowerPresentation
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNonemptyPrimitiveDeRhamTorsionTowerPresentation.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.nonempty_primitiveDeRhamTorsionTowerPresentation : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A), Nonempty (Dat t c) := by
  first | exact @GlobalTheory.PtExt.nonempty_dat | exact GlobalTheory.PtExt.nonempty_dat | (intros; apply GlobalTheory.PtExt.nonempty_dat <;> assumption)
