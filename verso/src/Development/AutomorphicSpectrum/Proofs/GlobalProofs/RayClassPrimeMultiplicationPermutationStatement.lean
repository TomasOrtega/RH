import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassPrimeMultiplicationPermutation
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FRayClassPrimeMultiplicationPermutation.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.ray_class_prime_multiplication_permutation : ∀ (F : Type) [Field F] [NumberField F] (𝔣 𝔠 : Ideal (𝓞 F)) (S : Finset (Ideal (𝓞 F))), 𝔣 ≠ ⊥ → 𝔠.IsPrime → 𝔠 ≠ ⊥ → 𝔠 ⊔ 𝔣 = ⊤ →
  (∀ a ∈ S, CoprimeTo F 𝔣 a) → (∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) → (∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a) →
  ∃ τ : Equiv.Perm S, ∀ c : S,
    ∃ e : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I (τ c).1} ≃
        {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1) ∧ I ≤ 𝔠},
      ∀ J, (e J).1 = 𝔠 * J.1 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.shift_perm | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.shift_perm | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.shift_perm <;> assumption)
