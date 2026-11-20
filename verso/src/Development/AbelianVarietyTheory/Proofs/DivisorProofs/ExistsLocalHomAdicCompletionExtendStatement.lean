import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomAdicCompletionExtend
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLocalHomAdicCompletionExtend.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_comp : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (φ : A →+* R), IsLocalHom φ → ∃ ψ : AdicCompletion (maximalIdeal A) A →+* R, IsLocalHom ψ ∧ ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) = φ := by
  first | exact @GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend | exact GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend | (intros; apply GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend <;> assumption)
