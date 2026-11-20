import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMap
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsCommFormalGroupLawMap.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.isCommFormalGroupLaw_map : ∀ (R S : Type) [CommRing R] [CommRing S] (σ : R →+* S) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → IsLaw (fun i => MvPowerSeries.map σ (μ i)) := by
  first | exact @GlobalTheory.Katz.isLaw_map | exact GlobalTheory.Katz.isLaw_map | (intros; apply GlobalTheory.Katz.isLaw_map <;> assumption)
