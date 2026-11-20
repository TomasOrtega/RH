import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Evaluate the numerical expressions. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Loc.hsNE : UpperTheory.V.Z.Sym.Loc.HsNE := by
  intro O K _ _ _ _ _ Δ τ hL _ t
  have h2 : (2 : K) ≠ 0 := by
    have h := hL.two.map (algebraMap O K)
    rw [map_ofNat] at h
    exact h.ne_zero
  have hiff : hs (τ ^ 2 - 4) (t : K) = 1 ↔ ∃ a b : K, a ^ 2 - (τ ^ 2 - 4) * b ^ 2 = t := by
    unfold hs
    split_ifs with h
    · simp [h]
    · simp only [h, iff_false]
      norm_num
  rw [hiff]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : QuadraticAlgebra.norm (z : QuadraticAlgebra K (-1) τ) = (t : K) := by
      have h := congrArg Units.val hz
      rwa [Units.coe_map] at h
    refine ⟨((z : QuadraticAlgebra K (-1) τ).re * 2 + τ * (z : QuadraticAlgebra K (-1) τ).im) / 2,
      (z : QuadraticAlgebra K (-1) τ).im / 2, ?_⟩
    rw [← hz', norm_def]
    field_simp
    ring
  · rintro ⟨a, b, hab⟩
    have hw : QuadraticAlgebra.norm (⟨a - τ * b, 2 * b⟩ : QuadraticAlgebra K (-1) τ) = (t : K) := by
      rw [← hab, norm_def]
      ring
    have hu : IsUnit (⟨a - τ * b, 2 * b⟩ : QuadraticAlgebra K (-1) τ) := by
      rw [isUnit_iff_norm_isUnit, hw]
      exact t.isUnit
    refine ⟨hu.unit, ?_⟩
    ext
    rw [Units.coe_map, IsUnit.unit_spec]
    exact hw
