import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorsionFreeGenerators.RankOneStep

namespace PI.FGTFG

/- English proof (translation)
Introduce `R M _ _ _ _ _ _`. Establish `htor : Submodule.torsion R M = ⊥`. Use `eq_bot_iff.mpr fun x hx => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `(Submodule.mem_torsion_iff x).mp hx`. Rewrite `ha` using `[Submonoid.smul_def, smul_eq_zero]`.

Conclude with `(Submodule.mem_bot R).mpr (ha.resolve_left (nonZeroDivisors.coe_ne_zero a))`. Use `haveI : Module.Flat R M := IsDedekindDomain.flat_iff_torsion_eq_bot.mpr htor`. Use `haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M`. Conclude with `Module.Flat.projective_of_finitePresentation`.
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
