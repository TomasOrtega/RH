import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionUnramifiedNormal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCompletionUnramifiedNormal.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.completion_unramified_normal : ∀ (D E : Type) [CommRing D] [IsDomain D] [IsLocalRing D] [CommRing E] [IsLocalRing E] (h : D →+* E), IsNoetherianRing D → IsDomain (AdicCompletion (IsLocalRing.maximalIdeal D) D) → IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal D) D) → IsNoetherianRing E → IsAdicComplete (IsLocalRing.maximalIdeal E) E → IsLocalHom h → GlobalTheory.Toroidal.IsEtaleCompletion h → ((IsLocalRing.residue E).comp h).FormallyUnramified → IsDomain E ∧ IsIntegrallyClosed E := by
  first | exact @GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed | exact GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed | (intros; apply GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed <;> assumption)
