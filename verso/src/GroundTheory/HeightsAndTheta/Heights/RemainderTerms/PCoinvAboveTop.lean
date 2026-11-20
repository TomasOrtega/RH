import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

/- English proof (translation)
Introduce `K _ _ f n d H hH hd`. Take `⟨v, hv, hJ⟩` from `h1 K f n H`. Take `⟨Q, hQ, hcomp⟩` from `h2 K f n (H - v) hJ d`. Use `⟨Q, hQ, ?_⟩` and prove the remaining obligations. Establish `h0 : homogeneousComponent d v = 0` using `(h3 K f n v hv).1 d hd`.

Establish `hHd : homogeneousComponent d H = H`. Rewrite using `[homogeneousComponent_of_mem (mem_homogeneousSubmodule d H |>.mpr hH), if_pos rfl]`. Rewrite using `[← hcomp, map_sub, h0, sub_zero, hHd]`.
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
