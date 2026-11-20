import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.Development

noncomputable section

open NumberField Matrix IsDedekindDomain Formalism.UG PI.InHHClassFin
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.InHHClassFin

/- English proof (translation)
Use `⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩` and prove the remaining obligations. Use `show ((1 : I.Gf) : GL (Fin I.n) _) ∈ Formalism.UG.stabGL I.Lf`. Simplify using `using (Formalism.UG.stabGL I.Lf).one_mem`. Simplify using `[Formalism.MainNotions.S.AutInst.fmat]`.
-/
theorem one_mem_Kg (I : Formalism.MainNotions.S.AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
  · show ((1 : I.Gf) : GL (Fin I.n) _) ∈ Formalism.UG.stabGL I.Lf
    simpa using (Formalism.UG.stabGL I.Lf).one_mem
  · simp [Formalism.MainNotions.S.AutInst.fmat]

/- English proof (translation)
Introduce `I g x hg`. Use `letI := I.topf`. Use `haveI := I.topf_group`. Establish `hK : I.Kg g ∈ nhds (1 : I.Gf)` using `(I.topf_open g hg).mem_nhds (one_mem_Kg I g)`. Establish `hc : Continuous fun h : I.Gf => x⁻¹ * h * x` using `by fun_prop`.

Establish `hT : {h : I.Gf | x⁻¹ * h * x ∈ I.Kg g} ∈ nhds (1 : I.Gf)`. Establish `hK' : I.Kg g ∈ nhds (x⁻¹ * 1 * x)` using `by simpa using hK`. Conclude with `hc.continuousAt hK'`. Take `⟨g', hg', hsub⟩` from `I.topf_basis _ hT`. Conclude with `⟨g', hg', fun h hh => hsub hh⟩`.
-/
theorem kgNhd : KgNhd := by
  intro I g x hg
  letI := I.topf
  haveI := I.topf_group
  have hK : I.Kg g ∈ nhds (1 : I.Gf) := (I.topf_open g hg).mem_nhds (one_mem_Kg I g)
  have hc : Continuous fun h : I.Gf => x⁻¹ * h * x := by fun_prop
  have hT : {h : I.Gf | x⁻¹ * h * x ∈ I.Kg g} ∈ nhds (1 : I.Gf) := by
    have hK' : I.Kg g ∈ nhds (x⁻¹ * 1 * x) := by simpa using hK
    exact hc.continuousAt hK'
  obtain ⟨g', hg', hsub⟩ := I.topf_basis _ hT
  exact ⟨g', hg', fun h hh => hsub hh⟩

end PI.UnitaryGroupMassFormula.InHHClassFin
