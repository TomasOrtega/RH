import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af
open scoped MatrixGroups ModularForm

/- English proof (translation)
Introduce `N k _ χ f hχ hv h0`. Establish `hT : (1:ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods`. Rewrite using `[Subgroup.mem_strictPeriods_iff]`. Use `⟨ModularGroup.T, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, Gamma1_mem]`.

Simplify using `[ModularGroup.T]`. Use extensionality with `i j`. Rewrite using `[Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [ModularGroup.T]`. Establish `hinf : IsZeroAtImInfty f`.

Apply `ModularForm.isZeroAtImInfty_of_valueAtInfty_eq_zero f` to reduce the goal to its premises. Rewrite using `[← qExpansion_coeff_zero one_pos (ModularFormClass.analyticAt_cuspFunction_zero f one_pos hT) (SlashInvariantFormClass.periodic_comp_ofComplex f hT)]`. Conclude with `h0`. Use `⟨⟨f.toSlashInvariantForm, f.holo', fun {c} hc => ?_⟩, rfl⟩` and prove the remaining obligations. Establish `hc' : IsCusp c 𝒮ℒ`.

Rewrite `hc` using `[Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]`. Then use the resulting hypothesis. Rewrite using `[OnePoint.isZeroAt_iff_forall_SL2Z hc']`. Introduce `γ _`. Distinguish the cases in `hd : (N:ℤ) ∣ γ 1 0`. Establish `hγ : γ ∈ Gamma0 N` using `Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hd)`.

Express the relevant statement in the definitionally equal form `IsZeroAtImInfty (⇑f ∣[(k:ℤ)] γ)`. Rewrite using `[hχ γ hγ]`. Conclude with `hinf.smul _`. Conclude with `hv γ hd`.
-/
theorem UpperTheory.V.Sd.cuspOf :
    UpperTheory.V.Sd.CuspOf := by
  intro N k _ χ f hχ hv h0
  have hT : (1:ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff]
    refine ⟨ModularGroup.T, ?_, ?_⟩
    · rw [SetLike.mem_coe, Gamma1_mem]
      simp [ModularGroup.T]
    · ext i j
      rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
      fin_cases i <;> fin_cases j <;> simp [ModularGroup.T]
  have hinf : IsZeroAtImInfty f := by
    apply ModularForm.isZeroAtImInfty_of_valueAtInfty_eq_zero f
    rw [← qExpansion_coeff_zero one_pos (ModularFormClass.analyticAt_cuspFunction_zero f one_pos hT)
      (SlashInvariantFormClass.periodic_comp_ofComplex f hT)]
    exact h0
  refine ⟨⟨f.toSlashInvariantForm, f.holo', fun {c} hc => ?_⟩, rfl⟩
  have hc' : IsCusp c 𝒮ℒ := by
    rwa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc']
  intro γ _
  by_cases hd : (N:ℤ) ∣ γ 1 0
  · have hγ : γ ∈ Gamma0 N := Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hd)
    change IsZeroAtImInfty (⇑f ∣[(k:ℤ)] γ)
    rw [hχ γ hγ]
    exact hinf.smul _
  · exact hv γ hd
