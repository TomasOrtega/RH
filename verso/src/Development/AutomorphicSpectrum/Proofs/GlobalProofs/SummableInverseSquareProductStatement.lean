import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableInverseSquareProduct
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_prod_inv_one_add_sq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FSummableInverseSquareProduct.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.summable_inverse_square_product : ∀ r : ℕ, Summable (fun m : Fin r → ℕ => ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_prod_inv_one_add_sq | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_prod_inv_one_add_sq | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_prod_inv_one_add_sq <;> assumption)
