import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Establish `hdim : ∀ e, MahlerSectionDim e`. Introduce `e`. Proceed by induction on `e with`. Consider the case `zero => exact h₁ 0 h₂`. Consider the case `succ e ih => exact h₁ (e + 1) (h₃ e ih)`.

Introduce `n e δ h Z f u hprime hchow hhom hadm`. Conclude with `hdim e n δ h Z f u ⟨hprime, hchow, hhom⟩ hadm`.
-/
theorem MahlerSection.proof (h₁ : MahlerSectionOfConst.Statement) (h₂ : DefectConstZero.Statement)
    (h₃ : DefectConstStep.Statement) : MahlerSection.Statement := by
  have hdim : ∀ e, MahlerSectionDim e := by
    intro e
    induction e with
    | zero => exact h₁ 0 h₂
    | succ e ih => exact h₁ (e + 1) (h₃ e ih)
  intro n e δ h Z f u hprime hchow hhom hadm
  exact hdim e n δ h Z f u ⟨hprime, hchow, hhom⟩ hadm

end GroundTheory.Heights₂.Heights
