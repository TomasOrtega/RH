import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSqLocalizationOfPderivMem
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemSqLocalizationOfPderivMem.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.exists_not_mem_mul_mem_sq_of_pderiv_mem : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) → ∀ x ∈ Q, (∀ s, MvPolynomial.pderiv s x ∈ Q) → ∃ g, g ∉ Q ∧ g * x ∈ Q ^ 2 := by
  first | exact @GlobalTheory.mem_sq_localization_of_pderiv_mem | exact GlobalTheory.mem_sq_localization_of_pderiv_mem | (intros; apply GlobalTheory.mem_sq_localization_of_pderiv_mem <;> assumption)
