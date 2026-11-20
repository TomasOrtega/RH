import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInjectiveRingHomIsLocalHomAndExtend
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.finite_injective_localHom_and_extend` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteInjectiveRingHomIsLocalHomAndExtend.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.finite_injective_ringHom_isLocalHom_and_extend : ∀ (V R K : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [IsAlgClosed K] (ρ : V →+* R), Function.Injective ρ → ρ.Finite → IsLocalHom ρ ∧ ∀ ev : V →+* K, ∃ ev₁ : R →+* K, ev₁.comp ρ = ev := by
  first | exact @GlobalTheory.finite_injective_localHom_and_extend | exact GlobalTheory.finite_injective_localHom_and_extend | (intros; apply GlobalTheory.finite_injective_localHom_and_extend <;> assumption)
