import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.NablaBasis

noncomputable section

namespace PI.SlopeSteps

open MvPolynomial Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `N ν`. Establish `hfg` using `Formalism.L2.DIV.we_nabla_fg N N ν`. Establish `: Module.Finite ℤ (dualWeyl ℤ N N ν)` using `Module.Finite.iff_fg.mpr hfg`. Conclude with `⟨_, ⟨(Module.Free.chooseBasis ℤ (dualWeyl ℤ N N ν)).reindex (Fintype.equivFin _)⟩⟩`.
-/
theorem nabla_operator_basis : NablaBasis := by
  intro N ν
  have hfg := Formalism.L2.DIV.we_nabla_fg N N ν
  have : Module.Finite ℤ (dualWeyl ℤ N N ν) := Module.Finite.iff_fg.mpr hfg
  exact ⟨_, ⟨(Module.Free.chooseBasis ℤ (dualWeyl ℤ N N ν)).reindex (Fintype.equivFin _)⟩⟩

end PI.SlopeSteps
