import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicRingEquivAdicCompletionPlaceUnramifiedDegre
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPadicRingEquivAdicCompletionPlaceUnramifiedDegre.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.padic_ringEquiv_adicCompletion_place_unramified_degree_one : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) [Fact g.Prime] (w : HeightOneSpectrum (𝓞 E))
    (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ((g : ℕ) : 𝓞 E) ∈ w.asIdeal ∧ ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 ∧ Formalism.ConjugateSelfDual.normV w = g := by
  first | exact @GlobalTheory.LocalFieldIso.padic_iso_place | exact GlobalTheory.LocalFieldIso.padic_iso_place | (intros; apply GlobalTheory.LocalFieldIso.padic_iso_place <;> assumption)
