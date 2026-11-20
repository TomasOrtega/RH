import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapEqOfContinuousAdicCompletionIso
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FComapEqOfContinuousAdicCompletionIso.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.comap_eq_of_continuous_adicCompletion_iso : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) → w'.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal := by
  first | exact @GlobalTheory.PlaceOver.comap_eq_of_continuous_iso | exact GlobalTheory.PlaceOver.comap_eq_of_continuous_iso | (intros; apply GlobalTheory.PlaceOver.comap_eq_of_continuous_iso <;> assumption)
