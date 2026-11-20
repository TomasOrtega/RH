import Mathlib
import ReciprocityTheory.DualLattices.NearIdentityColengthStatement

namespace ReciprocityTheory.PGsh

open Matrix

section

variable {K : Type} [Field K] {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

private noncomputable def invPerm (e : G ≃ AddChar G K) : Equiv.Perm G :=
  Function.Involutive.toPerm (fun h => e.symm (e h)⁻¹) (fun h => by simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma invPerm_apply (e : G ≃ AddChar G K) (h : G) :
    invPerm e h = e.symm (e h)⁻¹ := rfl

/- English proof (translation)
Use extensionality with `g h`. Establish `key : ∀ x, e g x * e h x = (e g * e h) x` using `fun x => (AddChar.mul_apply _ _ _).symm`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, smul_eq_mul, key]`. Distinguish the cases in `hgh : e g * e h = 1`. Establish `h1 : invPerm e g = h`.

Rewrite using `[invPerm_apply, inv_eq_of_mul_eq_one_right hgh, Equiv.symm_apply_apply]`. Rewrite using `[if_pos h1, hgh]`. Simplify using the standard rewrite rules. Establish `h1 : ¬ invPerm e g = h`. Introduce `h1`.

Apply `hgh` to reduce the goal to its premises. Rewrite `h1` using `[invPerm_apply]`. Rewrite using `[← h1, Equiv.apply_symm_apply, mul_inv_cancel]`. Rewrite using `[if_neg h1, AddChar.sum_eq_zero_of_ne_one hgh, mul_zero]`.
-/
private lemma transpose_mul_self (e : G ≃ AddChar G K) :
    (Matrix.of fun g h : G => e h g)ᵀ * (Matrix.of fun g h : G => e h g) =
      (Fintype.card G : K) • (invPerm e).permMatrix K := by
  ext g h
  have key : ∀ x, e g x * e h x = (e g * e h) x := fun x => (AddChar.mul_apply _ _ _).symm
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, smul_eq_mul, key]
  by_cases hgh : e g * e h = 1
  · have h1 : invPerm e g = h := by
      rw [invPerm_apply, inv_eq_of_mul_eq_one_right hgh, Equiv.symm_apply_apply]
    rw [if_pos h1, hgh]
    simp
  · have h1 : ¬ invPerm e g = h := by
      intro h1
      apply hgh
      rw [invPerm_apply] at h1
      rw [← h1, Equiv.apply_symm_apply, mul_inv_cancel]
    rw [if_neg h1, AddChar.sum_eq_zero_of_ne_one hgh, mul_zero]

/- English proof (translation)
Establish `h` using `congrArg Matrix.det (transpose_mul_self e)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_permutation]`. Rewrite using `[sq]`. Conclude with `h`.
-/
private lemma det_sq (e : G ≃ AddChar G K) :
    (Matrix.of fun g h : G => e h g).det ^ 2 =
      (Fintype.card G : K) ^ Fintype.card G * (Equiv.Perm.sign (invPerm e) : K) := by
  have h := congrArg Matrix.det (transpose_mul_self e)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_permutation] at h
  rw [sq]
  exact h

end

/- English proof (translation)
Introduce `K _ G _ _ _ e`. Rewrite using `[det_sq e]`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (invPerm e)) with h | h <;> rw [h]`. Use `left`. Simplify using the standard rewrite rules.

Use `right`. Simplify using the standard rewrite rules.
-/
theorem charTable : CharTableStatement := by
  intro K _ G _ _ _ e
  rw [det_sq e]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (invPerm e)) with h | h <;> rw [h]
  · left; simp
  · right; simp

end ReciprocityTheory.PGsh
