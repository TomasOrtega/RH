import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb
open scoped ContDiff

/- English proof (translation)
Introduce `E _ _ _ a φ hφ g`. Rewrite using `[IsExpLieAlgebra.isSmoothFun_iff]`. Introduce `x`. Set `L0 : ArchMatrix E a →ₗ[ℝ] TR.Lie E a` to `(matEq E a).symm.toLinearMap`. Set `L : ArchMatrix E a →L[ℝ] TR.Lie E a` to `LinearMap.toContinuousLinearMap L0`.

Establish `hL : ∀ z : archGroup E a, L ((z : (ArchMatrix E a)ˣ) : ArchMatrix E a) = TR.toL ((grpEq E a).symm z).val`. Introduce `z`. Take `⟨y, rfl⟩` from `(grpEq E a).surjective z`. Rewrite using `[MulEquiv.symm_apply_apply, coe_grpEq]`. Conclude with `(matEq E a).symm_apply_apply y.val`.

Establish `hexp : ContDiff ℝ ∞ (NormedSpace.exp : ArchMatrix E a → ArchMatrix E a)` using `contDiff_iff_contDiffAt.2 fun X => (NormedSpace.exp_analytic (𝕂 := ℝ) X).contDiffAt`. Establish `hc : ContDiff ℝ ∞ fun Y : archLie E a => L (((x * (isExpLieAlgebra E a).expG Y : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a)` using `L.contDiff.comp (contDiff_const.mul (hexp.comp (archLie E a).subtypeL.contDiff))`. Establish `e : (fun Y : archLie E a => archSlice φ g (x * (isExpLieAlgebra E a).expG Y)) = fun Y : archLie E a => TR.chart φ g (L (((x * (isExpLieAlgebra E a).expG Y : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a))`. Use function extensionality and compare the values at `Y`. Rewrite using `[hL, TR.chart_val, ← infEmb_grpEq, MulEquiv.apply_symm_apply]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Use `contDiff_iff_contDiffAt.2 fun Y => (TR.contDiffAt_chart hφ g ?_).comp Y hc.contDiffAt` and prove the remaining obligations. Rewrite using `[hL]`. Conclude with `TR.val_mem_invSet _`.
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
