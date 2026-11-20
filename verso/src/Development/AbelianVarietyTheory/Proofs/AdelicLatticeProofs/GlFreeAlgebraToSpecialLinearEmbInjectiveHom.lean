import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.EmbHom

variable {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
  [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A)

/- English proof (translation)
Use extensionality with `⟨i, x⟩ ⟨j, y⟩`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[res, Matrix.one_apply]`. Simplify using `[res, Matrix.one_apply, h]`.
-/
theorem res_one' : res b (1 : Matrix κ κ A) = 1 := by
  ext ⟨i, x⟩ ⟨j, y⟩
  by_cases h : i = j
  · subst h
    simp [res, Matrix.one_apply]
  · simp [res, Matrix.one_apply, h]

omit [DecidableEq κ] in
/- English proof (translation)
Use extensionality with `⟨i, x⟩ ⟨j, y⟩`. Simplify using `only [res, Matrix.of_apply, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply, Fintype.sum_prod_type]`.
-/
theorem res_mul' (g h : Matrix κ κ A) : res b (g * h) = res b g * res b h := by
  ext ⟨i, x⟩ ⟨j, y⟩
  simp only [res, Matrix.of_apply, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply,
    Fintype.sum_prod_type]

omit [Fintype κ] [DecidableEq κ] in
/- English proof (translation)
Use extensionality with `i j`. Apply `Algebra.leftMulMatrix_injective b` to reduce the goal to its premises. Use extensionality with `x y`. Conclude with `congrFun (congrFun e (i, x)) (j, y)`.
-/
theorem res_inj' (g h : Matrix κ κ A) (e : res b g = res b h) : g = h := by
  ext i j
  apply Algebra.leftMulMatrix_injective b
  ext x y
  exact congrFun (congrFun e (i, x)) (j, y)

/- English proof (translation)
Unfold `emb`. Rewrite using `[inv_one, Units.val_one, res_one', Matrix.det_one, ← Matrix.fromBlocks_one]`. Use `congr 1`.
-/
theorem emb_one' : emb b (1 : GL κ A) = 1 := by
  unfold emb
  rw [inv_one, Units.val_one, res_one', Matrix.det_one, ← Matrix.fromBlocks_one]
  congr 1

/- English proof (translation)
Unfold `emb`. Rewrite using `[Matrix.fromBlocks_multiply, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, res_mul', res_mul', Matrix.det_mul]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `[Matrix.mul_apply, mul_comm]`.
-/
theorem emb_mul' (g h : GL κ A) : emb b (g * h) = emb b g * emb b h := by
  unfold emb
  rw [Matrix.fromBlocks_multiply, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, res_mul', res_mul',
    Matrix.det_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  ext i j
  simp [Matrix.mul_apply, mul_comm]

/- English proof (translation)
Unfold `emb`. Rewrite using `[Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique (n := Unit), Matrix.of_apply, ← Matrix.det_mul, ← res_mul', Units.mul_inv, res_one', Matrix.det_one]`.
-/
theorem emb_det' (g : GL κ A) : (emb b g).det = 1 := by
  unfold emb
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique (n := Unit), Matrix.of_apply, ← Matrix.det_mul, ← res_mul',
    Units.mul_inv, res_one', Matrix.det_one]

/- English proof (translation)
Establish `h1 : emb b g * emb b g⁻¹ = 1` using `by rw [← emb_mul', mul_inv_cancel, emb_one']`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, Matrix.adjugate_mul, emb_det', one_smul, Matrix.one_mul]`.
-/
theorem emb_adjugate' (g : GL κ A) : (emb b g).adjugate = emb b g⁻¹ := by
  have h1 : emb b g * emb b g⁻¹ = 1 := by rw [← emb_mul', mul_inv_cancel, emb_one']
  calc (emb b g).adjugate = (emb b g).adjugate * (emb b g * emb b g⁻¹) := by rw [h1, Matrix.mul_one]
    _ = emb b g⁻¹ := by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, emb_det', one_smul, Matrix.one_mul]

/- English proof (translation)
Introduce `g h e`. Apply `Units.ext` to reduce the goal to its premises. Apply `res_inj' b` to reduce the goal to its premises. Conclude with `(Matrix.fromBlocks_inj.mp e).1`.
-/
theorem emb_injective' : Function.Injective (fun g : GL κ A => emb b g) := by
  intro g h e
  apply Units.ext
  apply res_inj' b
  exact (Matrix.fromBlocks_inj.mp e).1

/- English proof (translation)
Introduce `R A β κ _ _ _ _ _ _ _ b`. Conclude with `⟨emb_one' b, emb_mul' b, fun g => ⟨emb_det' b g, emb_adjugate' b g⟩, emb_injective' b⟩`.
-/
theorem emb_hom : ∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A), emb b (1 : GL κ A) = 1 ∧ (∀ g h : GL κ A, emb b (g * h) = emb b g * emb b h) ∧ (∀ g : GL κ A, (emb b g).det = 1 ∧ (emb b g).adjugate = emb b g⁻¹) ∧ Function.Injective (fun g : GL κ A => emb b g) := by
  intro R A β κ _ _ _ _ _ _ _ b
  exact ⟨emb_one' b, emb_mul' b, fun g => ⟨emb_det' b g, emb_adjugate' b g⟩, emb_injective' b⟩

end GlobalTheory.ClassFin.EmbHom
