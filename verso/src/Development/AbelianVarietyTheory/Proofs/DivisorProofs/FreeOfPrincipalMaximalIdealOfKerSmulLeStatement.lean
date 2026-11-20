import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfPrincipalMaximalIdealOfKerSmulLe
import Mathlib
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFreeOfPrincipalMaximalIdealOfKerSmulLe.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.free_of_principal_maximalIdeal_of_ker_smul_le' : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : R), IsLocalRing.maximalIdeal R = Ideal.span {x} → ∀ (N : Type 1) [AddCommGroup N] [Module R N], Module.Finite R N → (∀ n : N, x • n = 0 → n ∈ Ideal.span {a : R | x * a = 0} • (⊤ : Submodule R N)) → Module.Free R N := by
  first | exact @GlobalTheory.free_of_principal_maximalIdeal_of_ker_smul_le | exact GlobalTheory.free_of_principal_maximalIdeal_of_ker_smul_le | (intros; apply GlobalTheory.free_of_principal_maximalIdeal_of_ker_smul_le <;> assumption)
