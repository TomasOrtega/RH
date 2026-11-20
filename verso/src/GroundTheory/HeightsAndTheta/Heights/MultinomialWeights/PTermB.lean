import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

/- English proof (translation)
Introduce `d S u g B0 _hyp _hB0 hM5 Q hQ`. Take `⟨hsum, hle⟩` from `hM5 Q hQ`. Establish `hsum' : Summable (fun p : primesAbove S B0 => ‖rest₂ d S.vol (p : ℕ) (S.frob p) Q‖)`. Simplify `hsum` using `[Real.norm_eq_abs]`. Establish `h1 : ‖restTot S B0 Q‖ ≤ ∑' p : primesAbove S B0, ‖rest₂ d S.vol (p : ℕ) (S.frob p) Q‖` using `norm_tsum_le_tsum_norm hsum'`.

Establish `h2 : |restTot S B0 Q| ≤ ∑' p : primesAbove S B0, |rest₂ d S.vol (p : ℕ) (S.frob p) Q|`. Simplify `h1` using `[Real.norm_eq_abs]`. Conclude with `h2.trans hle`.
-/
theorem TermB.proof : TermB.Statement := by
  intro d S u g B0 _hyp _hB0 hM5 Q hQ
  obtain ⟨hsum, hle⟩ := hM5 Q hQ
  have hsum' : Summable (fun p : primesAbove S B0 =>
      ‖rest₂ d S.vol (p : ℕ) (S.frob p) Q‖) := by
    simpa [Real.norm_eq_abs] using hsum
  have h1 : ‖restTot S B0 Q‖ ≤ ∑' p : primesAbove S B0, ‖rest₂ d S.vol (p : ℕ) (S.frob p) Q‖ :=
    norm_tsum_le_tsum_norm hsum'
  have h2 : |restTot S B0 Q| ≤ ∑' p : primesAbove S B0, |rest₂ d S.vol (p : ℕ) (S.frob p) Q| := by
    simpa [Real.norm_eq_abs] using h1
  exact h2.trans hle

end GroundTheory.Heights₂.Heights.TheoremB
