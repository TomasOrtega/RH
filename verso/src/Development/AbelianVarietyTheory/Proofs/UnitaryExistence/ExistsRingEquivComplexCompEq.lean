import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis

namespace GlobalTheory.CompRat

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem exists_ringEquiv_complex_comp_eq :
    ∀ (k : Type) [Field k] [Countable k] (φ ψ : k →+* ℂ), ∃ τ : ℂ ≃+* ℂ, ∀ x, τ (φ x) = ψ x :=
  fun _ _ _ φ ψ => GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq φ ψ

end GlobalTheory.CompRat
