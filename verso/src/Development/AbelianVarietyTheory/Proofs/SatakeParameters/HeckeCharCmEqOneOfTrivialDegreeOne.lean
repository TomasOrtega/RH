import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharInfTrivialOfTrivAtDegOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharTrivialAtPlaceOfDegOneCofiniteTrivialStatement

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

namespace GlobalTheory.HeckeSplit

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ χ hχ hdeg`. Establish `hinf` using `GlobalTheory.T.heckeChar_inf_trivial_of_trivAt_degOne F E χ hχ hdeg`. Establish `hfin` using `GlobalTheory.T.heckeChar_trivialAtPlace_of_degOne_cofinite_trivial F E χ hχ hdeg hinf`. Use `ext1 x`. Establish `hfact` using `(GlobalTheory.T.continuous_ideleChar_local_factorization E χ hχ.1).2.2 x ∅ (fun v _ => hfin v _)`.

Rewrite using `[hfact, hinf]`. Simplify using the standard rewrite rules.
-/
theorem heckeChar_eq_one_of_degOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]
    [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ →
    (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → χ = 1 := by
  intro F E _ _ _ _ _ _ _ _ χ hχ hdeg
  have hinf := GlobalTheory.T.heckeChar_inf_trivial_of_trivAt_degOne F E χ hχ hdeg
  have hfin := GlobalTheory.T.heckeChar_trivialAtPlace_of_degOne_cofinite_trivial F E χ hχ hdeg hinf
  ext1 x
  have hfact := (GlobalTheory.T.continuous_ideleChar_local_factorization E χ hχ.1).2.2 x ∅ (fun v _ => hfin v _)
  rw [hfact, hinf]
  simp

end GlobalTheory.HeckeSplit
