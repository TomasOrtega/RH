import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DirectSumCancelRight
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WeilDeligne.WD.lpSum_cancel_right` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FDirectSumCancelRight.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.directSum_cancel_right : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a b c : WD h), a.lpSum c = b.lpSum c → a = b := by
  first | exact @GlobalTheory.WeilDeligne.WD.lpSum_cancel_right | exact GlobalTheory.WeilDeligne.WD.lpSum_cancel_right | (intros; apply GlobalTheory.WeilDeligne.WD.lpSum_cancel_right <;> assumption)
