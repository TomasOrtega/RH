import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalTranslationCompCommutingOperator
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocFactor.exists_locRep_comp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsLocalTranslationCompCommutingOperator.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.exists_localTranslation_comp_commuting_operator : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (o : GlobalTheory.CuspRep.Op E a), ∃ (g : GL (Fin a) (w.adicCompletion E)) (T : Module.End ℂ π.V), (∀ h, T ∘ₗ π.locRep w h = π.locRep w h ∘ₗ T) ∧ π.op o = π.locRep w g ∘ₗ T := by
  first | exact @GlobalTheory.LocFactor.exists_locRep_comp | exact GlobalTheory.LocFactor.exists_locRep_comp | (intros; apply GlobalTheory.LocFactor.exists_locRep_comp <;> assumption)
