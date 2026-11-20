import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAInModPSplit

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem imA_eps'_eq (p : TypX X) :
    1 - epsP X p = PI.FinKW.psiV X.B.I p.1 (sigA X.B.I X.ew) := by
  have h := imA_ew_split X p
  rw [epsP]
  linear_combination -h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem imA_bw_eps (p : TypX X) (i : Fin D.R.k) :
    epsP X p • PI.FinKW.vecV X.B.I p.1 (X.bw i) = PI.FinKW.vecV X.B.I p.1 (X.bw i) := by
  conv_rhs => rw [X.bw_w i]
  rw [imA_vecV_smul']

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem imA_bw_eps' (p : TypX X) (i : Fin D.R.k) :
    (1 - epsP X p) • PI.FinKW.vecV X.B.I p.1 (X.bw i) = 0 := by
  rw [sub_smul, one_smul, imA_bw_eps, sub_self]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem imA_bwd_eps' (p : TypX X) (i : Fin D.R.k) :
    (1 - epsP X p) • PI.FinKW.vecV X.B.I p.1 (X.bwd i) = PI.FinKW.vecV X.B.I p.1 (X.bwd i) := by
  conv_rhs => rw [X.bwd_w i]
  rw [imA_vecV_smul', imA_eps'_eq]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem imA_bwd_eps (p : TypX X) (i : Fin D.R.k) :
    epsP X p • PI.FinKW.vecV X.B.I p.1 (X.bwd i) = 0 := by
  have h := imA_bwd_eps' X p i
  rw [sub_smul, one_smul, sub_eq_self] at h
  exact h

end MassDataIdxSteps
