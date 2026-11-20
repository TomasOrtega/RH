import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdicCompletionValuationMapUniformiser
import Mathlib
open ValuativeRel NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.adicCompletion_valuation_map_uniformiser` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FAdicCompletionValuationMapUniformiser.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.valued_v_map_irreducible_eq_ofAdd_neg_one : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → ∀ ϖ : 𝒪[k], Irreducible ϖ → Valued.v (φ (ϖ : k)) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  first | exact @GlobalTheory.adicCompletion_valuation_map_uniformiser | exact GlobalTheory.adicCompletion_valuation_map_uniformiser | (intros; apply GlobalTheory.adicCompletion_valuation_map_uniformiser <;> assumption)
