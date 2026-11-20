import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldMapsLocalRingUnique
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FNumberFieldMapsLocalRingUnique.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.number_field_maps_local_ring_unique : ∀ (K : Type) [Field K] [NumberField K] (B : Type) [CommRing B] [IsLocalRing B] (Ω : Type) [Field Ω] (π : B →+* Ω) (s t : K →+* B), π.comp s = π.comp t → s = t := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq | exact GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq | (intros; apply GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq <;> assumption)
