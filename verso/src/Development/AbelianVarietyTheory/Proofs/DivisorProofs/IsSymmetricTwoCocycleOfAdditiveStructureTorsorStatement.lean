import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricTwoCocycleOfAdditiveStructureTorsor
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsSymmetricTwoCocycleOfAdditiveStructureTorsor.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.isSymmetricTwoCocycle_of_additiveStructure_torsor : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (f : Fn1 A) (g : Fn2 A), IsAdd f g → IsSymCoc g := by
  first | exact @GlobalTheory.PtExt.isSymCoc_of_isAdd | exact GlobalTheory.PtExt.isSymCoc_of_isAdd | (intros; apply GlobalTheory.PtExt.isSymCoc_of_isAdd <;> assumption)
