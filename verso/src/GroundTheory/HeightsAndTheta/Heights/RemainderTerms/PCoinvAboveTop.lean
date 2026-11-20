import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem CoinvAboveTop.proof (h1 : CoinvPolynomialReduction.Statement)
    (h2 : CoinvIdealComponent.Statement) (h3 : CoinvStaircaseComponent.Statement) :
    CoinvAboveTop.Statement := by
  intro K _ _ f n d H hH hd
  obtain ⟨v, hv, hJ⟩ := h1 K f n H
  obtain ⟨Q, hQ, hcomp⟩ := h2 K f n (H - v) hJ d
  refine ⟨Q, hQ, ?_⟩
  have h0 : homogeneousComponent d v = 0 := (h3 K f n v hv).1 d hd
  have hHd : homogeneousComponent d H = H := by
    rw [homogeneousComponent_of_mem (mem_homogeneousSubmodule d H |>.mpr hH), if_pos rfl]
  rw [← hcomp, map_sub, h0, sub_zero, hHd]

end GroundTheory.Heights₂.Heights.RestTerms
