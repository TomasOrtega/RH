import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspidalLabelPolynomialUniqueAllPrimes
import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonListLength
open CategoryTheory Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GLq.isCuspOf_label_unique_allPrimes` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCuspidalLabelPolynomialUniqueAllPrimes.lean&line=155#L155)
-/
theorem _root_.GlobalTheory.T.cuspidal_label_polynomial_unique_all_primes : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (d : ℕ) (P P' : (ZMod g)[X]) (χ : GlobalTheory.GLq.Gn g d → ℂ), GlobalTheory.GLq.IsCuspOf L P χ → GlobalTheory.GLq.IsCuspOf L P' χ → P = P' := by
  first | exact @GlobalTheory.GLq.isCuspOf_label_unique_allPrimes | exact GlobalTheory.GLq.isCuspOf_label_unique_allPrimes | (intros; apply GlobalTheory.GLq.isCuspOf_label_unique_allPrimes <;> assumption)
