import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemRangeOfSurjectiveLocalizedMap
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_smul_mem_range_of_surjective_localization_map` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSmulMemRangeOfSurjectiveLocalizedMap.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_smul_mem_range_of_surjective_localized_map : ∀ (R A B : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B), Function.Surjective (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ) → ∀ b : B, ∃ t ∉ p, t • b ∈ ψ.range := by
  first | exact @GlobalTheory.exists_smul_mem_range_of_surjective_localization_map | exact GlobalTheory.exists_smul_mem_range_of_surjective_localization_map | (intros; apply GlobalTheory.exists_smul_mem_range_of_surjective_localization_map <;> assumption)
