import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormValueOnTangentVectorEqZeroOfGlobalFormZero
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamComparisonBijectiveCupSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparisonStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormValueOnTangentVectorEqZeroOfGlobalFormZero.lean&line=156#L156)
-/
theorem _root_.GlobalTheory.T.formValueOnTangentVector_eq_zero_of_globalForm_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) (v : epsR R ⟶ A) (f : Form (A.hom ≫ 𝟙 (Sp R))), GlobalTheory.CechDR.cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → tanVal v f = 0 := by
  first | exact @GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero | exact GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero | (intros; apply GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero <;> assumption)
