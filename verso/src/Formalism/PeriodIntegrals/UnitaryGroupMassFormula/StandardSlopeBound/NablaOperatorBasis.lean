import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.NablaBasis

noncomputable section

namespace PI.SlopeSteps

open MvPolynomial Formalism.GradedWeylDivisibility

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem nabla_operator_basis : NablaBasis := by
  intro N ν
  have hfg := Formalism.L2.DIV.we_nabla_fg N N ν
  have : Module.Finite ℤ (dualWeyl ℤ N N ν) := Module.Finite.iff_fg.mpr hfg
  exact ⟨_, ⟨(Module.Free.chooseBasis ℤ (dualWeyl ℤ N N ν)).reindex (Fintype.equivFin _)⟩⟩

end PI.SlopeSteps
