import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfWeierstrassPDerivWeierstrassPTorsionEqStatement

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.SepGL

/- English proof (translation)
Introduce `h`. Apply `hx` to reduce the goal to its premises. Establish `h2 : (x ᵥ* (α : Matrix (Fin 2) (Fin 2) (ZMod N))) ᵥ* ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = x`. Rewrite using `[Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]`. Unfold `vmul at h`.

Rewrite using `[← h2, h, Matrix.zero_vecMul]`.
-/
theorem vmul_ne_zero {N : ℕ} (x : Fin 2 → ZMod N) (hx : x ≠ 0) (α : GL (Fin 2) (ZMod N)) :
    vmul x α ≠ 0 := by
  intro h
  apply hx
  have h2 : (x ᵥ* (α : Matrix (Fin 2) (Fin 2) (ZMod N))) ᵥ*
      ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = x := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  unfold vmul at h
  rw [← h2, h, Matrix.zero_vecMul]

/- English proof (translation)
Introduce `N _ τ α β h`. Break down `subsingleton_or_nontrivial (ZMod N) with hs | hs` into its components or cases. Conclude with `Matrix.GeneralLinearGroup.ext fun i j => Subsingleton.elim _ _`. Establish `key : ∀ i : Fin 2, vmul (Pi.single i 1) α = vmul (Pi.single i 1) β`. Introduce `i`.

Establish `h0 : (Pi.single i (1 : ZMod N) : Fin 2 → ZMod N) ≠ 0`. Introduce `h1`. Use `congrFun h1 i` as an intermediate fact. Simplify using `at this`. Conclude with `GlobalTheory.T.eq_of_weierstrassP_derivWeierstrassP_torsion_eq N τ _ _ (vmul_ne_zero _ h0 α) (vmul_ne_zero _ h0 β) (h i).1 (h i).2`.

Use `Matrix.GeneralLinearGroup.ext fun i j => ?_` and prove the remaining obligations. Use `congrFun (key i) j` as an intermediate fact. Simplify `this` using `[vmul, Matrix.single_vecMul]`.
-/
theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (α β : GL (Fin 2) (ZMod N)), (∀ i : Fin 2, wp N (vmul (Pi.single i 1) α) τ = wp N (vmul (Pi.single i 1) β) τ ∧ wpd N (vmul (Pi.single i 1) α) τ = wpd N (vmul (Pi.single i 1) β) τ) → α = β := by
  intro N _ τ α β h
  rcases subsingleton_or_nontrivial (ZMod N) with hs | hs
  · exact Matrix.GeneralLinearGroup.ext fun i j => Subsingleton.elim _ _
  · have key : ∀ i : Fin 2, vmul (Pi.single i 1) α = vmul (Pi.single i 1) β := by
      intro i
      have h0 : (Pi.single i (1 : ZMod N) : Fin 2 → ZMod N) ≠ 0 := by
        intro h1
        have := congrFun h1 i
        simp at this
      exact GlobalTheory.T.eq_of_weierstrassP_derivWeierstrassP_torsion_eq N τ _ _ (vmul_ne_zero _ h0 α) (vmul_ne_zero _ h0 β) (h i).1 (h i).2
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    have := congrFun (key i) j
    simpa [vmul, Matrix.single_vecMul] using this

end GlobalTheory.WpFam.SepGL
