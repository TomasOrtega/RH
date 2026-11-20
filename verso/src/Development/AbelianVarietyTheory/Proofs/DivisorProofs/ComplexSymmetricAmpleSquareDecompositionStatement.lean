import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexSymmetricAmpleSquareDecomposition
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SqDecC.sqDec_complex` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FComplexSymmetricAmpleSquareDecomposition.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.complex_symmetricAmple_square_decomposition : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → SqDec A L M := by
  first | exact @GlobalTheory.SqDecC.sqDec_complex | exact GlobalTheory.SqDecC.sqDec_complex | (intros; apply GlobalTheory.SqDecC.sqDec_complex <;> assumption)
