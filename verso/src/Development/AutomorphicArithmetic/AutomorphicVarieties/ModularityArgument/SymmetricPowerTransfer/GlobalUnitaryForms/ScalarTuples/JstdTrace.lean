import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DOrb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GConj

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem jstd_trace {K : Type} [Field K] (τ : K) : (jstd τ ω).trace = τ := by
  simp [jstd, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis_repr_apply,
    QuadraticAlgebra.basis, Module.Basis.coe_ofEquivFun]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem toUnit_val {R : Type} [Monoid R] {x : R} (h : IsUnit x) : ((toUnit x : Rˣ) : R) = x := by
  simp [toUnit, h]

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem omega_unit {K : Type} [Field K] (τ : K) : IsUnit (ω : Etau K τ) := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (by simp [QuadraticAlgebra.norm_def])

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Glob.locD :
    UpperTheory.V.Z.Sym.Glob.LocD := by
  intro O K _ _ _ _ _ Δ τ L hτ γ j hγ hj χ hχ z hz
  obtain ⟨j', hj'tr, hS, hK⟩ := dOrb O K Δ τ L hτ γ j hγ hj
  have hc := gConj O K Δ τ L hτ j' (jstd τ) hj'tr (jstd_trace τ)
  have hunr1 : Unr O (1 : Kˣ →* ℂˣ) := fun u => rfl
  have hzu : toUnit (1 + ω : Etau K τ) = z := by
    apply Units.ext
    rw [toUnit_val (by rw [← hz]; exact z.isUnit), hz]
  refine ⟨?_, ?_⟩
  · rw [← hc.2 1 hunr1]
    exact hS _ (toUnit_val (omega_unit τ))
  · rw [hzu, ← hc.2 χ hχ]
    exact hK χ hχ z
