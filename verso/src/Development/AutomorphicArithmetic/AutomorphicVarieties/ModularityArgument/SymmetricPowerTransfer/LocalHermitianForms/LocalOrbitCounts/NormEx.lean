import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenOfNorm

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Loc.normEx : UpperTheory.V.Z.Sym.Loc.NormEx := by
  intro O K _ _ _ _ _ Δ L u
  obtain ⟨ε, s, hs, e⟩ := L.even
  obtain ⟨a, b, h⟩ := L.nm_unit ε u
  have h' : algebraMap O K a ^ 2 - algebraMap O K ε * algebraMap O K b ^ 2 = algebraMap O K u := by
    rw [← h]; simp
  refine ⟨⟨algebraMap O K a, algebraMap O K b / s⟩, ?_, ?_⟩
  · have e1 : (⟨algebraMap O K a, algebraMap O K b / s⟩ : Lsq K Δ) = algebraMap O _ a + algebraMap O _ b * ⟨0, 1 / s⟩ := by
      rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ), IsScalarTower.algebraMap_apply O K (Lsq K Δ) b]
      ext <;> simp [div_eq_mul_inv]
    rw [e1]
    refine isIntegral_algebraMap.add (isIntegral_algebraMap.mul (IsIntegral.of_pow (n := 2) (by norm_num) ?_))
    have : (⟨0, 1 / s⟩ : Lsq K Δ) ^ 2 = algebraMap O _ (ε : O) := by
      rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
      ext <;> simp [sq]
      rw [e]; field_simp
    rw [this]; exact isIntegral_algebraMap
  · rw [QuadraticAlgebra.norm_def, ← h']
    simp only
    rw [e]; field_simp; ring
