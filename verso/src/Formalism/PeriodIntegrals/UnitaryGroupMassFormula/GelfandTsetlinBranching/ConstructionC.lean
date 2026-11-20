import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.NatWAntiC

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem realize_of (h : PI.HwIrred) (he : ExtremalFacts) (ha : FixedLine) (hb : StableCompl)
    (hc : HighestVec) : Realize := by
  intro n N hN lam mu f hf hfix hne
  subst hN
  exact realize_C h he ha n lam mu f hf hfix hne

end PI.WGB
