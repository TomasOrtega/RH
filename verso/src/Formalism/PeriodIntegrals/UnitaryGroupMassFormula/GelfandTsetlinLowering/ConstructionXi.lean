import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.EvalInitMinorNormLe

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

/- English proof (translation)
Introduce `n N h lam sg hI`. Use `⟨XiB.xi_ne h lam sg, XiB.xi_mem h lam sg hI, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hlow hdiag`. Conclude with `XiB.xi_unitri h lam sg g hlow hdiag`. Introduce `t`.

Conclude with `XiB.xi_torus h lam sg hI t`. Introduce `a`. Conclude with `XiB.xi_last h lam sg hI a`. Introduce `x hx`. Conclude with `XiB.xi_unitary h lam sg x hx`.
-/
theorem xi_coefficient_facts : XiFacts := by
  intro n N h lam sg hI
  refine ⟨XiB.xi_ne h lam sg, XiB.xi_mem h lam sg hI, ?_, ?_, ?_, ?_⟩
  · intro g hlow hdiag
    exact XiB.xi_unitri h lam sg g hlow hdiag
  · intro t
    exact XiB.xi_torus h lam sg hI t
  · intro a
    exact XiB.xi_last h lam sg hI a
  · intro x hx
    exact XiB.xi_unitary h lam sg x hx

end PI.WGL
