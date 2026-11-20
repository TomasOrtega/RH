import Mathlib

namespace Reformulated.TransposeInverseTheory

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

def transposeInvFun (g : GL n R) : GL n R where
  val := ((g⁻¹ : GL n R) : Matrix n n R)ᵀ
  inv := (g : Matrix n n R)ᵀ
  val_inv := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  inv_val := by rw [← transpose_mul, Units.inv_mul, transpose_one]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
theorem transposeInvFun_involutive :
    Function.Involutive (transposeInvFun : GL n R → GL n R) := by
  intro g
  apply Units.ext
  exact transpose_transpose _

def transposeInv : GL n R ≃* GL n R where
  toFun := transposeInvFun
  invFun := transposeInvFun
  left_inv := transposeInvFun_involutive
  right_inv := transposeInvFun_involutive
  map_mul' g h := by
    apply Units.ext
    change (((g * h)⁻¹ : GL n R) : Matrix n n R)ᵀ =
      ((g⁻¹ : GL n R) : Matrix n n R)ᵀ * ((h⁻¹ : GL n R) : Matrix n n R)ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, transpose_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_transposeInv (g : GL n R) :
    ((transposeInv g : GL n R) : Matrix n n R) = ((g⁻¹ : GL n R) : Matrix n n R)ᵀ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_transposeInv_inv (g : GL n R) :
    (((transposeInv g)⁻¹ : GL n R) : Matrix n n R) = (g : Matrix n n R)ᵀ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem transposeInv_apply (g : GL n R) (i j : n) :
    (transposeInv g : GL n R) i j = (g⁻¹ : GL n R) j i := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
@[simp] theorem transposeInv_transposeInv (g : GL n R) :
    transposeInv (transposeInv g) = g := transposeInvFun_involutive g

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem transposeInv_symm : (transposeInv : GL n R ≃* GL n R).symm = transposeInv := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.
-/
theorem det_transposeInv (g : GL n R) :
    GeneralLinearGroup.det (transposeInv g) = (GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  apply Units.ext
  simp only [GeneralLinearGroup.val_det_apply, coe_transposeInv, det_transpose]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Both sides reduce to the same expression.
-/
theorem map_transposeInv {S : Type*} [CommRing S] (f : R →+* S) (g : GL n R) :
    GeneralLinearGroup.map f (transposeInv g) = transposeInv (GeneralLinearGroup.map f g) := by
  apply Units.ext
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem continuous_transposeInv [TopologicalSpace R] :
    Continuous (transposeInv : GL n R → GL n R) := by
  rw [Units.continuous_iff]
  exact ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

end Reformulated.TransposeInverseTheory
