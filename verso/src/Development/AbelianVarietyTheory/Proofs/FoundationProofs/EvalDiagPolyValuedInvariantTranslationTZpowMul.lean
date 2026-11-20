import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalPolyDegreeSlashAction
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

/- English proof (translation)
Establish `hm : mat (ModularGroup.T ^ (n : ℤ)) = !![1, (n : ℤ); 0, 1]` using `ModularGroup.coe_T_zpow _`. Establish `hc : ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = (τ : ℂ) + n`. Rewrite using `[UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← hT τ, eval_polySlash w _ _ _ (hV _), hm, hc]`. Simplify using `only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]`. Use `push_cast`. Simplify using the standard rewrite rules. Rewrite using `[hm]`.

Simplify using the standard rewrite rules.
-/
theorem evalDiag_T_step (w n : ℕ) (V : ℍ → ℂ[X]) (hV : ∀ τ, V τ ∈ degreeLT ℂ (w + 1))
    (hT : ∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ)
    (τ : ℍ) :
    (V (ModularGroup.T ^ (n : ℤ) • τ)).eval ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = (V τ).eval (τ : ℂ) := by
  have hm : mat (ModularGroup.T ^ (n : ℤ)) = !![1, (n : ℤ); 0, 1] := ModularGroup.coe_T_zpow _
  have hc : ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = (τ : ℂ) + n := by
    rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
    push_cast; ring
  rw [← hT τ, eval_polySlash w _ _ _ (hV _), hm, hc]
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    push_cast
    simp
  · rw [hm]
    simp

/- English proof (translation)
Introduce `w n V hV hT m`. Establish `step` using `evalDiag_T_step w n V hV hT`. Simplify using `only [zpow_mul]`. Proceed by induction on `m using Int.induction_on with`. Consider the case `zero => intro τ`.

Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `τ`. Rewrite using `[zpow_add_one, mul_smul, ih, step]`. Consider the case `pred k ih`.

Introduce `τ`. Establish `e : (ModularGroup.T ^ (n : ℤ)) ^ (-(k : ℤ) - 1) • τ = (ModularGroup.T ^ (n : ℤ)) ^ (-(k : ℤ)) • ((ModularGroup.T ^ (n : ℤ))⁻¹ • τ)`. Rewrite using `[zpow_sub_one, mul_smul]`. Rewrite using `[e, ih, ← step ((ModularGroup.T ^ (n : ℤ))⁻¹ • τ), smul_inv_smul]`.
-/
theorem evalDiag_T_invariant : ∀ (w n : ℕ) (V : ℍ → ℂ[X]), (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) → (∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) → ∀ (m : ℤ) (τ : ℍ), (V (ModularGroup.T ^ ((n : ℤ) * m) • τ)).eval ((ModularGroup.T ^ ((n : ℤ) * m) • τ : ℍ) : ℂ) = (V τ).eval (τ : ℂ) := by
  intro w n V hV hT m
  have step := evalDiag_T_step w n V hV hT
  simp only [zpow_mul]
  induction m using Int.induction_on with
  | zero => intro τ; simp
  | succ k ih =>
    intro τ
    rw [zpow_add_one, mul_smul, ih, step]
  | pred k ih =>
    intro τ
    have e : (ModularGroup.T ^ (n : ℤ)) ^ (-(k : ℤ) - 1) • τ =
        (ModularGroup.T ^ (n : ℤ)) ^ (-(k : ℤ)) • ((ModularGroup.T ^ (n : ℤ))⁻¹ • τ) := by
      rw [zpow_sub_one, mul_smul]
    rw [e, ih, ← step ((ModularGroup.T ^ (n : ℤ))⁻¹ • τ), smul_inv_smul]

end GlobalTheory.HeckeFamilyMatrices
