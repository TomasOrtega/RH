import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusSemilinearCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
open GlobalTheory.RingChain
open scoped TensorProduct Pointwise ChangeOfRings
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFrobeniusSemilinearCompatible.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.frobenius_semilinear_compatible : ∀ (p k : ℕ) [Fact p.Prime] (A R : Type) [CommRing A] [CommRing R] [Algebra A R], ModIso R (p : A) → ∀ (M N M' N' : Type) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N'] (Φ : M →ₛₗ[algebraMap A R] M') (Ψ : N →ₛₗ[algebraMap A R] N'), Function.Bijective Φ → Function.Bijective Ψ → ∀ (ψ : M →+ N) (ψ' : M' →+ N'), (∀ x, Ψ (ψ x) = ψ' (Φ x)) → IsFrobLin R p (p ^ k) ψ' → IsFrobLin A p (p ^ k) ψ := by
  first | exact @GlobalTheory.RingChain.FrobTr.isFrobLin_of_modIso | exact GlobalTheory.RingChain.FrobTr.isFrobLin_of_modIso | (intros; apply GlobalTheory.RingChain.FrobTr.isFrobLin_of_modIso <;> assumption)
