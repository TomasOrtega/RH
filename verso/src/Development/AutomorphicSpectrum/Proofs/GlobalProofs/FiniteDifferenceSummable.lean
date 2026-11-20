import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

/- English proof (translation)
Establish `hinj : Function.Injective (fun m : Fin r → ℕ => m + Pi.single i 1)` using `fun a b h => add_right_cancel h`. Conclude with `(hg.comp_injective hinj).sub hg`.
-/
theorem summable_fd {r : ℕ} (i : Fin r) (g : (Fin r → ℕ) → ℂ) (hg : Summable g) :
    Summable (fd i g) := by
  have hinj : Function.Injective (fun m : Fin r → ℕ => m + Pi.single i 1) :=
    fun a b h => add_right_cancel h
  exact (hg.comp_injective hinj).sub hg

/- English proof (translation)
Introduce `r cs g hg`. Proceed by induction on `cs with`. Consider the case `nil => simpa [DL] using hg`. Consider the case `cons c cs ih`. Establish `: DL (c :: cs) g = fd c (DL cs g)` using `rfl`.

Rewrite using `[this]`. Conclude with `summable_fd c _ ih`.
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
