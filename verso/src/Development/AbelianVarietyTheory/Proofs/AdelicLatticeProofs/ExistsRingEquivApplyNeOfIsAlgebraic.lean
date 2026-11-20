import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Introduce `z _ hz`. Assume the negation of the conclusion as `h`. Establish `hfix : ∀ σ : ℂ ≃ₐ[ℚ] ℂ, σ z = z` using `fun σ => by_contra fun hne => h ⟨σ.toRingEquiv, hne⟩`. Take `⟨q, hq⟩` from `GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := ℚ) z hfix`. Conclude with `hz q (hq.symm.trans (by simp))`.
-/
theorem exists_ringEquiv_apply_ne_of_isAlgebraic :
    ∀ z : ℂ, IsAlgebraic ℚ z → (∀ q : ℚ, z ≠ q) → ∃ σ : ℂ ≃+* ℂ, σ z ≠ z := by
  intro z _ hz
  by_contra h
  have hfix : ∀ σ : ℂ ≃ₐ[ℚ] ℂ, σ z = z := fun σ => by_contra fun hne => h ⟨σ.toRingEquiv, hne⟩
  obtain ⟨q, hq⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := ℚ) z hfix
  exact hz q (hq.symm.trans (by simp))

end GlobalTheory.ClassFin
