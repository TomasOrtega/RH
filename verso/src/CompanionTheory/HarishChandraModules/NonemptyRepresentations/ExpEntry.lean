import Mathlib

noncomputable section

namespace CompanionTheory.D.Inhab

/- English proof (translation)
Set `_` to `Matrix.linftyOpNormedRing (n := Fin N) (α := ℂ)`. Set `_` to `Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℂ)`. Establish `: CompleteSpace (Matrix (Fin N) (Fin N) ℂ)` using `FiniteDimensional.complete ℝ _`. Establish `h` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0`. Simplify using `only [zero_smul, NormedSpace.exp_zero, one_mul] at h`.

Set `L0 : Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] ℂ` to `{ toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Set `L : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℂ` to `LinearMap.toContinuousLinearMap L0`. Establish `h2` using `L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h`. Establish `e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) = L ∘ fun u : ℝ => NormedSpace.exp (u • X)`. Use function extensionality and compare the values at `t`.

Simplify using `only [Function.comp_apply, Complex.coe_smul]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `h2`.
-/
theorem exp_entry (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) (X i j) 0 := by
  let _ := Matrix.linftyOpNormedRing (n := Fin N) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℂ)
  have : CompleteSpace (Matrix (Fin N) (Fin N) ℂ) := FiniteDimensional.complete ℝ _
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L0 : Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let L : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap L0
  have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) = L ∘ fun u : ℝ => NormedSpace.exp (u • X) := by
    funext t
    simp only [Function.comp_apply, Complex.coe_smul]
    rfl
  rw [e]
  exact h2

end CompanionTheory.D.Inhab
