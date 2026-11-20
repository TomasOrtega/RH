import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CmpValBaseChangeSimilitude
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

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FThetaLawProofs%2FCmpValBaseChangeSimilitude.lean&line=292#L292)
-/
theorem _root_.GlobalTheory.T.l2ComparisonNumber_baseChange_similitude_alt : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ w (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (hg : x'.P.g = x.P.g) (b : Fin (m ^ x.P.g) → RR x m) (b' : Fin (m ^ x'.P.g) → RR x' m) (lam : Rˣ), al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → KeyVia x' x f φ w → (∀ k, SecVia x' x φ w (b' k) (b (k.cast (by rw [hg])))) → IsSquareDeterminantComparison x m al b lam → IsSquareDeterminantComparison x' m al b' (Units.map f.toMonoidHom lam) := by
  first | exact @GlobalTheory.SimilBaseChange.cmpVal_baseChange_similitude | exact GlobalTheory.SimilBaseChange.cmpVal_baseChange_similitude | (intros; apply GlobalTheory.SimilBaseChange.cmpVal_baseChange_similitude <;> assumption)
