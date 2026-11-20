import Formalism.LocalToGlobal.Columns.ChainInst

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Ext

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem clL_toMatrix_mul {n : ℕ} (κ : Sp E n ≃ₗ[E] Sp E n) :
    LinearMap.toMatrix' κ.toLinearMap * LinearMap.toMatrix' κ.symm.toLinearMap = 1 := by
  rw [← LinearMap.toMatrix'_comp]
  have : κ.toLinearMap ∘ₗ κ.symm.toLinearMap = LinearMap.id := by
    ext x
    simp
  rw [this, LinearMap.toMatrix'_id]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem clL_toMatrix_mul' {n : ℕ} (κ : Sp E n ≃ₗ[E] Sp E n) :
    LinearMap.toMatrix' κ.symm.toLinearMap * LinearMap.toMatrix' κ.toLinearMap = 1 := by
  rw [← LinearMap.toMatrix'_comp]
  have : κ.symm.toLinearMap ∘ₗ κ.toLinearMap = LinearMap.id := by
    ext x
    simp
  rw [this, LinearMap.toMatrix'_id]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem clL_extM_mul {n : ℕ} (c : ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) :
    ciExtM c (LinearMap.toMatrix' κ.toLinearMap) * ciExtM c (LinearMap.toMatrix' κ.symm.toLinearMap) = 1 := by
  rw [← ciExtM_mul, clL_toMatrix_mul, ciExtM_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem clL_extM_mul' {n : ℕ} (c : ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) :
    ciExtM c (LinearMap.toMatrix' κ.symm.toLinearMap) * ciExtM c (LinearMap.toMatrix' κ.toLinearMap) = 1 := by
  rw [← ciExtM_mul, clL_toMatrix_mul', ciExtM_one]

def clL_ext {n : ℕ} (c : ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) : Sp E (n + c) ≃ₗ[E] Sp E (n + c) :=
  ciEquiv (ciExtM c (LinearMap.toMatrix' κ.toLinearMap)) (ciExtM c (LinearMap.toMatrix' κ.symm.toLinearMap)) (clL_extM_mul c κ)
    (clL_extM_mul' c κ)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem clL_ext_apply {n : ℕ} (c : ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) (v : Sp E (n + c)) :
    clL_ext c κ v = (ciExtM c (LinearMap.toMatrix' κ.toLinearMap)).mulVec v :=
  ciEquiv_apply _ _ _ _ v

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem clL_ext_inX {n : ℕ} (c : ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) (x : Sp E n) :
    clL_ext c κ (Loc.inX E n c x) = Loc.inX E n c (κ x) := by
  rw [clL_ext_apply, ciExtM_inX]
  congr 1
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem clL_ext_natAdd {n : ℕ} (c : ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) (v : Sp E (n + c)) (i : Fin c) :
    clL_ext c κ v (Fin.natAdd n i) = v (Fin.natAdd n i) := by
  rw [clL_ext_apply, ciExtM_natAdd]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem clL_ext_det {n : ℕ} (c : ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) :
    ((LinearEquiv.det (clL_ext c κ) : Eˣ) : E) = ((LinearEquiv.det κ : Eˣ) : E) := by
  rw [LinearEquiv.coe_det, LinearEquiv.coe_det]
  have h1 : ((clL_ext c κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) : Sp E (n + c) →ₗ[E] Sp E (n + c)) =
      Matrix.toLin' (ciExtM c (LinearMap.toMatrix' κ.toLinearMap)) := by
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply]
    exact clL_ext_apply c κ v
  rw [h1, LinearMap.det_toLin', ← LinearMap.det_toMatrix' (κ : Sp E n →ₗ[E] Sp E n)]
  unfold ciExtM
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem clL_ext_symm {n : ℕ} (c : ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) : (clL_ext c κ).symm = clL_ext c κ.symm := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.symm_apply_eq, clL_ext_apply, clL_ext_apply, Matrix.mulVec_mulVec, ← ciExtM_mul, clL_toMatrix_mul, ciExtM_one,
    Matrix.one_mulVec]

end Ext

end Formalism.L2.Col
