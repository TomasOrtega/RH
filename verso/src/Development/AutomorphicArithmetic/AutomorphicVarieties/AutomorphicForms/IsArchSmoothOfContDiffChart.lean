import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb
open scoped ContDiff

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.isArchSmooth_of_contDiff_chart :
    UpperTheory.V.Fb.SmTo := by
  intro E _ _ _ a φ hφ g
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro x
  let L0 : ArchMatrix E a →ₗ[ℝ] TR.Lie E a := (matEq E a).symm.toLinearMap
  let L : ArchMatrix E a →L[ℝ] TR.Lie E a := LinearMap.toContinuousLinearMap L0
  have hL : ∀ z : archGroup E a, L ((z : (ArchMatrix E a)ˣ) : ArchMatrix E a) = TR.toL ((grpEq E a).symm z).val := by
    intro z
    obtain ⟨y, rfl⟩ := (grpEq E a).surjective z
    rw [MulEquiv.symm_apply_apply, coe_grpEq]
    exact (matEq E a).symm_apply_apply y.val
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : ArchMatrix E a → ArchMatrix E a) :=
    contDiff_iff_contDiffAt.2 fun X => (NormedSpace.exp_analytic (𝕂 := ℝ) X).contDiffAt
  have hc : ContDiff ℝ ∞ fun Y : archLie E a =>
      L (((x * (isExpLieAlgebra E a).expG Y : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) :=
    L.contDiff.comp (contDiff_const.mul (hexp.comp (archLie E a).subtypeL.contDiff))
  have e : (fun Y : archLie E a => archSlice φ g (x * (isExpLieAlgebra E a).expG Y)) = fun Y : archLie E a =>
      TR.chart φ g (L (((x * (isExpLieAlgebra E a).expG Y : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a)) := by
    funext Y
    rw [hL, TR.chart_val, ← infEmb_grpEq, MulEquiv.apply_symm_apply]
    rfl
  rw [e]
  refine contDiff_iff_contDiffAt.2 fun Y => (TR.contDiffAt_chart hφ g ?_).comp Y hc.contDiffAt
  rw [hL]
  exact TR.val_mem_invSet _
