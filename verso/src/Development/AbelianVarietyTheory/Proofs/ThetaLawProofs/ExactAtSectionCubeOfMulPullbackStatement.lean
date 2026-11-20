import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExactAtSectionCubeOfMulPullback
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

/- English proof (citation)
Apply `GlobalTheory.exactAt_secCube_of_mul_pull` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FThetaLawProofs%2FExactAtSectionCubeOfMulPullback.lean&line=188#L188)
-/
theorem _root_.GlobalTheory.T.exactAt_sectionCube_of_mul_pullback : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (m : ℕ) (N : LB P.A.left) (I : Type) [LinearOrder I] [Fintype I] (D : I → P.A.left.Opens) (p : ℕ), (m : K) ≠ 0 → N.IsLB → (cubeComplex (secCube P.A.hom (N.pull (Out.mulA P.A m).left) (fun i => (Out.mulA P.A m).left ⁻¹ᵁ D i))).ExactAt p → (cubeComplex (secCube P.A.hom N D)).ExactAt p := by
  first | exact @GlobalTheory.exactAt_secCube_of_mul_pull | exact GlobalTheory.exactAt_secCube_of_mul_pull | (intros; apply GlobalTheory.exactAt_secCube_of_mul_pull <;> assumption)
