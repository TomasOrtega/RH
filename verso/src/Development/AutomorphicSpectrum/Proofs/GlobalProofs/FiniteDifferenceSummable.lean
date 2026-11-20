import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem summable_fd {r : ℕ} (i : Fin r) (g : (Fin r → ℕ) → ℂ) (hg : Summable g) :
    Summable (fd i g) := by
  have hinj : Function.Injective (fun m : Fin r → ℕ => m + Pi.single i 1) :=
    fun a b h => add_right_cancel h
  exact (hg.comp_injective hinj).sub hg

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem summable_DL : ∀ (r : ℕ) (cs : List (Fin r)) (g : (Fin r → ℕ) → ℂ), Summable g →
    Summable (DL cs g) := by
  intro r cs g hg
  induction cs with
  | nil => simpa [DL] using hg
  | cons c cs ih =>
    have : DL (c :: cs) g = fd c (DL cs g) := rfl
    rw [this]
    exact summable_fd c _ ih

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
