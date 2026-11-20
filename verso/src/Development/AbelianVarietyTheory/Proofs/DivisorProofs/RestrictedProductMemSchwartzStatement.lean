import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AdelicCoordSB.finprod_mem_SB` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRestrictedProductMemSchwartz.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.restricted_product_mem_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
      GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  first | exact @GlobalTheory.AdelicCoordSB.finprod_mem_SB | exact GlobalTheory.AdelicCoordSB.finprod_mem_SB | (intros; apply GlobalTheory.AdelicCoordSB.finprod_mem_SB <;> assumption)
