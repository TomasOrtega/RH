import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParameterTensorOneDimInjective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WeilDeligne.lpChar_left_injective_of_lpDim_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FWeilDeligneParameterTensorOneDimInjective.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.weilDeligneParameter_tensor_oneDim_injective : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a b c : WD h), c.lpDim = 1 → a.lpChar c = b.lpChar c → a = b := by
  first | exact @GlobalTheory.WeilDeligne.lpChar_left_injective_of_lpDim_one | exact GlobalTheory.WeilDeligne.lpChar_left_injective_of_lpDim_one | (intros; apply GlobalTheory.WeilDeligne.lpChar_left_injective_of_lpDim_one <;> assumption)
