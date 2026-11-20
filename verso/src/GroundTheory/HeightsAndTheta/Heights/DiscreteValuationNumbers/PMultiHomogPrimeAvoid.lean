import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpLocRingFracCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RelevantMinimalOfDivCycleNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Introduce `R _ K _ _ ι S hfin hS`. Take `⟨e, L, hL, he, hLS⟩` from `exists_form_avoid_primes hfin.toFinset (fun W hW => hS W (hfin.mem_toFinset.mp hW)) (fun _ => 1)`. Conclude with `⟨e, L, hL, fun k => he k, fun Q hQ => hLS Q (hfin.mem_toFinset.mpr hQ)⟩`.
-/
theorem MultiHomogPrimeAvoid.proof : MultiHomogPrimeAvoid.Statement.{u} := by
  intro R _ K _ _ ι S hfin hS
  obtain ⟨e, L, hL, he, hLS⟩ := exists_form_avoid_primes hfin.toFinset
    (fun W hW => hS W (hfin.mem_toFinset.mp hW)) (fun _ => 1)
  exact ⟨e, L, hL, fun k => he k, fun Q hQ => hLS Q (hfin.mem_toFinset.mpr hQ)⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
