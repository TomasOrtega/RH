import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlacesIdempotentNearOneAdeles
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPlacesIdempotentNearOneAdeles.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.exists_placesIdempotent_near_one_adeles : ∀ (F : Type) [Field F] [NumberField F], ∀ U : Set (AF F), U ∈ 𝓝 (1 : AF F) → ∃ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε ∧ ε ∈ U := by
  first | exact @GlobalTheory.placesIdem_tendsto_one | exact GlobalTheory.placesIdem_tendsto_one | (intros; apply GlobalTheory.placesIdem_tendsto_one <;> assumption)
