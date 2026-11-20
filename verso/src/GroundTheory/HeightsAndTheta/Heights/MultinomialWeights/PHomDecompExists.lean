import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsHomDecomp
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Imports
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

/- English proof (translation)
Introduce `d F hF`. Take `⟨Q, hQ, hsum⟩` from `RestTerms.CoinvAboveTop.full ℚ d.f d.N (d.D + 1) F hF (by simp [RestTerms.Coinv.coinvTop, IndexData.D, RestTerms.topDegree])`. Use `⟨Q, hF, fun k _ τ => hQ k τ, ?_⟩` and prove the remaining obligations. Rewrite using `[RestTerms.IsPowerSumDecomposition, hsum]`. Both sides reduce to the same expression.
-/
theorem HomDecompExists.proof : HomDecompExists.Statement := by
  intro d F hF
  obtain ⟨Q, hQ, hsum⟩ := RestTerms.CoinvAboveTop.full ℚ d.f d.N (d.D + 1) F hF
    (by simp [RestTerms.Coinv.coinvTop, IndexData.D, RestTerms.topDegree])
  refine ⟨Q, hF, fun k _ τ => hQ k τ, ?_⟩
  rw [RestTerms.IsPowerSumDecomposition, hsum]
  rfl

end GroundTheory.Heights₂.Heights.TheoremB
