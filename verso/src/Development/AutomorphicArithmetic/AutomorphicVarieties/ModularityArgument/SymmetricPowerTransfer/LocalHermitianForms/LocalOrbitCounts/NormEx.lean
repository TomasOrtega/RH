import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenOfNorm

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ L u`. Take `⟨ε, s, hs, e⟩` from `L.even`. Take `⟨a, b, h⟩` from `L.nm_unit ε u`. Establish `h' : algebraMap O K a ^ 2 - algebraMap O K ε * algebraMap O K b ^ 2 = algebraMap O K u`. Rewrite using `[← h]`.

Simplify using the standard rewrite rules. Use `⟨⟨algebraMap O K a, algebraMap O K b / s⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `e1 : (⟨algebraMap O K a, algebraMap O K b / s⟩ : Lsq K Δ) = algebraMap O _ a + algebraMap O _ b * ⟨0, 1 / s⟩`. Rewrite using `[IsScalarTower.algebraMap_apply O K (Lsq K Δ), IsScalarTower.algebraMap_apply O K (Lsq K Δ) b]`. Apply the tactic sequence `ext <;> simp [div_eq_mul_inv]`.

Rewrite using `[e1]`. Use `isIntegral_algebraMap.add (isIntegral_algebraMap.mul (IsIntegral.of_pow (n := 2) (by norm_num) ?_))` and prove the remaining obligations. Establish `: (⟨0, 1 / s⟩ : Lsq K Δ) ^ 2 = algebraMap O _ (ε : O)`. Rewrite using `[IsScalarTower.algebraMap_apply O K (Lsq K Δ)]`. Apply the tactic sequence `ext <;> simp [sq]`.

Rewrite using `[e]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap`. Rewrite using `[QuadraticAlgebra.norm_def, ← h']`.

Simplify using `only`. Rewrite using `[e]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
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
