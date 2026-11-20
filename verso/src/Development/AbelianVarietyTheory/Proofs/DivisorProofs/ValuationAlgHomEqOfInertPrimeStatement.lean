import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgHomEqOfInertPrime
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FValuationAlgHomEqOfInertPrime.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.valuation_algHom_eq_of_inertPrime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ x : E, w.valuation E (σ x) = w.valuation E x := by
  first | exact @GlobalTheory.InertConjVal.val_conj | exact GlobalTheory.InertConjVal.val_conj | (intros; apply GlobalTheory.InertConjVal.val_conj <;> assumption)
