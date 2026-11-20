import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Loc.h90L : UpperTheory.V.Z.Sym.Loc.NormOneIsCoboundaryUnramifiedQuadratic := by
  intro O K _ _ _ _ _ Δ L β hβ
  haveI := L.frac
  have h2 := L.two_ne
  have h0 : Δ ≠ 0 := by
    obtain ⟨u, s, hs, e⟩ := L.even
    rw [e]
    exact mul_ne_zero (u.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero 2 hs)
  rw [QuadraticAlgebra.norm_def] at hβ
  by_cases h : 1 + β.re = 0
  · have h1 : β.re = -1 := by linear_combination h
    have h3 : β.im = 0 := by
      have : Δ * β.im ^ 2 = 0 := by rw [h1] at hβ; linear_combination -hβ
      simpa [h0] using this
    have hu : IsUnit (ω : Lsq K Δ) := QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (by simp [QuadraticAlgebra.norm_def, h0])
    exact ⟨hu.unit, by ext <;> simp [h1, h3]⟩
  · have hu : IsUnit (⟨1 + β.re, -β.im⟩ : Lsq K Δ) := QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (by
      have : QuadraticAlgebra.norm (⟨1 + β.re, -β.im⟩ : Lsq K Δ) = 2 * (1 + β.re) := by
        rw [QuadraticAlgebra.norm_def]; simp only; linear_combination hβ
      rw [this]; exact (mul_ne_zero h2 h).isUnit)
    refine ⟨hu.unit, ?_⟩
    ext
    · simp; linear_combination -hβ
    · simp; ring
