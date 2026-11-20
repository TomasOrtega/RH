import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorsionFreeGenerators.RankOneStep

namespace PI.FGTFG

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem projective_reduction : ProjStep := by
  intro R M _ _ _ _ _ _
  have htor : Submodule.torsion R M = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
    rw [Submonoid.smul_def, smul_eq_zero] at ha
    exact (Submodule.mem_bot R).mpr (ha.resolve_left (nonZeroDivisors.coe_ne_zero a))
  haveI : Module.Flat R M := IsDedekindDomain.flat_iff_torsion_eq_bot.mpr htor
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  exact Module.Flat.projective_of_finitePresentation

end PI.FGTFG
