import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharTrivialAtPlaceOfDegOneCofiniteTrivial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FHeckeCharTrivialAtPlaceOfDegOneCofiniteTrivial.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.heckeChar_trivialAtPlace_of_degOne_cofinite_trivial : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ → (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → (∀ x : (InfiniteAdeleRing E)ˣ, χ (infIdele E x) = 1) → ∀ w, TrivAt χ w := by
  first | exact @GlobalTheory.HeckeFin.trivAt_of_degOne_cofinite | exact GlobalTheory.HeckeFin.trivAt_of_degOne_cofinite | (intros; apply GlobalTheory.HeckeFin.trivAt_of_degOne_cofinite <;> assumption)
