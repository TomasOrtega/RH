import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLieAlgebraCoordinateLinearEquiv
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorusLieCoord.lieCoord_bijective_add_smul` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTorusLieAlgebraCoordinateLinearEquiv.lean&line=130#L130)
-/
theorem _root_.GlobalTheory.T.torus_lie_algebra_coordinate_linear_equiv : ∀ (R : Type) [CommRing R] (r : ℕ), Function.Bijective (lieCoord : LieG (torus R r) → Fin r → R) ∧ (∀ x y : LieG (torus R r), lieCoord (lieAdd _ x y) = lieCoord x + lieCoord y) ∧ ∀ (a : R) (x : LieG (torus R r)), lieCoord (lieScale _ a x) = a • lieCoord x := by
  first | exact @GlobalTheory.TorusLieCoord.lieCoord_bijective_add_smul | exact GlobalTheory.TorusLieCoord.lieCoord_bijective_add_smul | (intros; apply GlobalTheory.TorusLieCoord.lieCoord_bijective_add_smul <;> assumption)
