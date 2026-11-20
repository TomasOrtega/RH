import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionUniversalLocalHom
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ProjectionSurjective
open IsLocalRing GlobalTheory.Pat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCompletionUniversalLocalHom.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.completion_universal_local_hom : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] [IsAdicComplete (maximalIdeal S') S'] (q : Ideal R) [q.IsPrime] (φ : R →+* S) (ψ : R →+* S'), IsCplAt q φ → (maximalIdeal S').comap ψ = q → ∃! θ : S →+* S', IsLocalHom θ ∧ θ.comp φ = ψ := by
  first | exact @GlobalTheory.Pat.isCplAt_existsUnique_map | exact GlobalTheory.Pat.isCplAt_existsUnique_map | (intros; apply GlobalTheory.Pat.isCplAt_existsUnique_map <;> assumption)
