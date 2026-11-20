import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPointThetaPullbacksIsUnit
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

/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FThetaLawProofs%2FExistsPointThetaPullbacksIsUnit.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.exists_point_thetaPullbacks_isUnit : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ : Fin 4 → Pt x), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∃ y : 𝟙_ (Over (Sp K)) ⟶ Out.powObj x.P.A 4, ∀ (p : (𝟙_ (Over (Sp K))).left) J, Good x.P.L p J → ∀ r, IsUnit (gs (y.left ≫ (alMap x al r (ξ r)).left) p (x.P.L.U (J (y.left ≫ (alMap x al r (ξ r)).left))) (x.th.f (J (y.left ≫ (alMap x al r (ξ r)).left)))) := by
  first | exact @GlobalTheory.SimilNonvan.exists_pt_isUnit | exact GlobalTheory.SimilNonvan.exists_pt_isUnit | (intros; apply GlobalTheory.SimilNonvan.exists_pt_isUnit <;> assumption)
