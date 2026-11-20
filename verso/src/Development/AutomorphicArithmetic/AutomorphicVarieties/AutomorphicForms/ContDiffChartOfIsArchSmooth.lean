import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb
open scoped ContDiff Topology

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

private noncomputable def toArch (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) :
    TR.Lie E a →L[ℝ] ArchMatrix E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => matEq E a (Matrix.of X)
      map_add' := fun X Y => map_add (matEq E a) (Matrix.of X) (Matrix.of Y)
      map_smul' := fun c X => map_smul (matEq E a) c (Matrix.of X) }

/- English proof (translation)
Establish `h` using `((isExpLieAlgebra E a).isSmoothFun_iff).1 (hφ g) 1`. Use `set e := expPartialHomeomorph ℝ (ArchMatrix E a)`. Establish `h1 : toArch E a (TR.oneL E a) = 1` using `map_one (matEq E a)`. Establish `hn : e.target ∈ 𝓝 (toArch E a (TR.oneL E a))`. Rewrite using `[h1]`.

Conclude with `e.open_target.mem_nhds (one_mem_expPartialHomeomorph_target ℝ _)`. Establish `hl : ContDiffAt ℝ ∞ (fun x => subspaceProj (archLie E a) (e.symm (toArch E a x))) (TR.oneL E a)` using `(subspaceProj (archLie E a)).contDiff.contDiffAt.comp _ (((contDiffOn_expPartialHomeomorph_symm ℝ _).contDiffAt hn).comp _ (toArch E a).contDiff.contDiffAt)`. Use `(h.contDiffAt.comp _ hl).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [(toArch E a).continuous.continuousAt.preimage_mem_nhds hn, TR.isOpen_invSet.mem_nhds (TR.val_mem_invSet (1 : GL (Fin a) (TR.Rinf E)))] with x hx hu`. Take `⟨u, hu⟩` from `hu`.

Establish `hxu : x = TR.toL u.val` using `hu.symm`. Substitute `hxu` using the available equality. Rewrite using `[TR.chart_val, ← infEmb_grpEq]`. Simplify using `only [Function.comp_apply, archSlice_apply, one_mul]`. Use `congr 3`.

Use `Subtype.ext (Units.ext ?_)` and prove the remaining obligations. Rewrite using `[IsExpLieAlgebra.coe_expG, subspaceProj_of_mem Submodule.mem_top]`. Conclude with `(e.right_inv hx).symm`.
-/
private theorem contDiffAt_one {φ : GA E a → ℂ} (hφ : IsArchSmooth φ) (g : GA E a) :
    ContDiffAt ℝ ∞ (TR.chart φ g) (TR.oneL E a) := by
  have h := ((isExpLieAlgebra E a).isSmoothFun_iff).1 (hφ g) 1
  set e := expPartialHomeomorph ℝ (ArchMatrix E a)
  have h1 : toArch E a (TR.oneL E a) = 1 := map_one (matEq E a)
  have hn : e.target ∈ 𝓝 (toArch E a (TR.oneL E a)) := by
    rw [h1]; exact e.open_target.mem_nhds (one_mem_expPartialHomeomorph_target ℝ _)
  have hl : ContDiffAt ℝ ∞ (fun x => subspaceProj (archLie E a) (e.symm (toArch E a x))) (TR.oneL E a) :=
    (subspaceProj (archLie E a)).contDiff.contDiffAt.comp _
      (((contDiffOn_expPartialHomeomorph_symm ℝ _).contDiffAt hn).comp _ (toArch E a).contDiff.contDiffAt)
  refine (h.contDiffAt.comp _ hl).congr_of_eventuallyEq ?_
  filter_upwards [(toArch E a).continuous.continuousAt.preimage_mem_nhds hn,
    TR.isOpen_invSet.mem_nhds (TR.val_mem_invSet (1 : GL (Fin a) (TR.Rinf E)))] with x hx hu
  obtain ⟨u, hu⟩ := hu
  have hxu : x = TR.toL u.val := hu.symm
  subst hxu
  rw [TR.chart_val, ← infEmb_grpEq]
  simp only [Function.comp_apply, archSlice_apply, one_mul]
  congr 3
  refine Subtype.ext (Units.ext ?_)
  rw [IsExpLieAlgebra.coe_expG, subspaceProj_of_mem Submodule.mem_top]
  exact (e.right_inv hx).symm

end

/- English proof (translation)
Introduce `E _ _ _ a φ hφ g x hx`. Take `⟨u, hu⟩` from `hx`. Establish `hxu : x = TR.toL u.val` using `hu.symm`. Substitute `hxu` using the available equality. Establish `e : TR.chart φ g = TR.chart φ (g * TR.infGL E a u) ∘ TR.lmul (TR.toL (u⁻¹).val)`.

Rewrite using `[← TR.chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]`. Establish `e1 : TR.lmul (TR.toL (u⁻¹).val) (TR.toL u.val) = TR.oneL E a` using `u.inv_mul`. Rewrite using `[e]`. Use `(ContDiffAt.comp _ ?_ (TR.lmul (TR.toL (u⁻¹).val)).contDiff.contDiffAt).contDiffWithinAt` and prove the remaining obligations. Rewrite using `[e1]`.

Conclude with `contDiffAt_one hφ _`.
-/
theorem UpperTheory.contDiff_chart_of_isArchSmooth :
    UpperTheory.V.Fb.SmOf := by
  intro E _ _ _ a φ hφ g x hx
  obtain ⟨u, hu⟩ := hx
  have hxu : x = TR.toL u.val := hu.symm
  subst hxu
  have e : TR.chart φ g = TR.chart φ (g * TR.infGL E a u) ∘ TR.lmul (TR.toL (u⁻¹).val) := by
    rw [← TR.chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have e1 : TR.lmul (TR.toL (u⁻¹).val) (TR.toL u.val) = TR.oneL E a := u.inv_mul
  rw [e]
  refine (ContDiffAt.comp _ ?_ (TR.lmul (TR.toL (u⁻¹).val)).contDiff.contDiffAt).contDiffWithinAt
  rw [e1]
  exact contDiffAt_one hφ _
