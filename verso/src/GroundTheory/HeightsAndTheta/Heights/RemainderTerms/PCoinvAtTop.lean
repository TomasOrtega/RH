import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

/- English proof (translation)
Introduce `K _ _ f n H hH`. Take `⟨v, hv, hJ⟩` from `h1 K f n H`. Take `⟨Q, -, hQ⟩` from `h2 K f n (H - v) hJ (coinvTop f n)`. Take `⟨-, c, hc⟩` from `h3 K f n v hv`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Establish `hcomp : H - C c * monomial (staircase f n) 1 = homogeneousComponent (coinvTop f n) (H - v)`. Rewrite using `[map_sub, homogeneousComponent_eq_self hH, hc]`. Rewrite using `[hcomp, hQ]`. Use `Ideal.sum_mem _ fun m hm => Ideal.sum_mem _ fun b _ => ?_` and prove the remaining obligations. Rewrite `hm` using `[Finset.mem_Icc]`.

Conclude with `Ideal.mul_mem_right _ _ (bps_mem_psumIdeal b hm.1 hm.2)`.
-/
theorem CoinvAtTop.proof (h1 : CoinvPolynomialReduction.Statement)
    (h2 : CoinvIdealComponent.Statement) (h3 : CoinvStaircaseComponent.Statement) :
    CoinvAtTop.Statement := by
  intro K _ _ f n H hH
  obtain ⟨v, hv, hJ⟩ := h1 K f n H
  obtain ⟨Q, -, hQ⟩ := h2 K f n (H - v) hJ (coinvTop f n)
  obtain ⟨-, c, hc⟩ := h3 K f n v hv
  refine ⟨c, ?_⟩
  have hcomp : H - C c * monomial (staircase f n) 1 =
      homogeneousComponent (coinvTop f n) (H - v) := by
    rw [map_sub, homogeneousComponent_eq_self hH, hc]
  rw [hcomp, hQ]
  refine Ideal.sum_mem _ fun m hm => Ideal.sum_mem _ fun b _ => ?_
  rw [Finset.mem_Icc] at hm
  exact Ideal.mul_mem_right _ _ (bps_mem_psumIdeal b hm.1 hm.2)

end

end GroundTheory.Heights₂.Heights.RestTerms
