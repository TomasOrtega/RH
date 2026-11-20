import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharCmEqOneOfTrivialDegreeOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeSplit.heckeChar_eq_one_of_degOne` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FHeckeCharCmEqOneOfTrivialDegreeOne.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.heckeChar_cm_eq_one_of_trivial_degree_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ → (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → χ = 1 := by
  first | exact @GlobalTheory.HeckeSplit.heckeChar_eq_one_of_degOne | exact GlobalTheory.HeckeSplit.heckeChar_eq_one_of_degOne | (intros; apply GlobalTheory.HeckeSplit.heckeChar_eq_one_of_degOne <;> assumption)
