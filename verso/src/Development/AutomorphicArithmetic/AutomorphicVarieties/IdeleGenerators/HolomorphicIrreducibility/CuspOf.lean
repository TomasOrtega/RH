import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af
open scoped MatrixGroups ModularForm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
