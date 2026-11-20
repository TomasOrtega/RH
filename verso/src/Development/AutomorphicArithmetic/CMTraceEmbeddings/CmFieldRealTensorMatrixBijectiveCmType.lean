import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.OrientEv
import Development.AutomorphicArithmetic.CMTraceEmbeddings.CmFieldRealTensorBijectiveCmType

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed UpperTheory.Gal.W2.Seed.Ori
open scoped TensorProduct

private noncomputable def entL {E : Type} [Field E] [NumberField E] {n : ℕ} (i j : Fin n) :
    Matrix (Fin n) (Fin n) E →ₗ[ℚ] E where
  toFun x := x i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def sgL {E : Type} [Field E] [NumberField E] {n : ℕ} (i j : Fin n) :
    E →ₗ[ℚ] Matrix (Fin n) (Fin n) E where
  toFun x := Matrix.single i j x
  map_add' a b := by simp [Matrix.single_add]
  map_smul' q a := by simp [Matrix.smul_single]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r x`. Rewrite using `[LinearMap.baseChange_tmul, realTensorEvalAlgHom_tmul, evM_tmul]`. Express the relevant statement in the definitionally equal form `r • σ (x i j) = _`.

Simplify using the standard rewrite rules. Consider the case `add a b ha hb => simp only [map_add, ha, hb, Matrix.add_apply]`.
-/
private theorem evaluation_baseChange_entry {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* ℂ) (i j : Fin n)
    (z : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) :
    ev1 σ ((entL i j).baseChange ℝ z) = evM σ z i j := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, realTensorEvalAlgHom_tmul, evM_tmul]
    change r • σ (x i j) = _
    simp
  | add a b ha hb => simp only [map_add, ha, hb, Matrix.add_apply]

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r x`. Rewrite using `[LinearMap.baseChange_tmul, realTensorEvalAlgHom_tmul, evM_tmul]`. Use extensionality with `a b`.

Simplify using `[sgL, Matrix.single_apply]`. Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add, ha, hb, map_add, Matrix.single_add]`.
-/
private theorem evM_sg {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* ℂ) (i j : Fin n)
    (w : ℝ ⊗[ℚ] E) :
    evM σ ((sgL i j).baseChange ℝ w) = Matrix.single i j (ev1 σ w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, realTensorEvalAlgHom_tmul, evM_tmul]
    ext a b
    simp [sgL, Matrix.single_apply]
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb, map_add, Matrix.single_add]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r x`. Simplify using `only [LinearMap.baseChange_tmul]`. Use `conv_lhs => rw [Matrix.matrix_eq_sum_single x]`.

Simplify using `[TensorProduct.tmul_sum, entL, sgL]`. Both sides reduce to the same expression. Consider the case `add a b ha hb => conv_lhs => rw [ha, hb]`. Simplify using `only [map_add, ← Finset.sum_add_distrib]`.
-/
private theorem sum_sg_ent {E : Type} [Field E] [NumberField E] {n : ℕ}
    (z : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) :
    z = ∑ i, ∑ j, (sgL i j).baseChange ℝ ((entL i j).baseChange ℝ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [LinearMap.baseChange_tmul]
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    simp [TensorProduct.tmul_sum, entL, sgL]
    rfl
  | add a b ha hb =>
    conv_lhs => rw [ha, hb]
    simp only [map_add, ← Finset.sum_add_distrib]

/- English proof (translation)
Introduce `hT E _ _ _ A n`. Establish `hb` using `UpperTheory.cmField_real_tensor_bijective_cmType hT A`. Prove the components needed by the constructor for the conclusion. Introduce `z₁ z₂ h`. Establish `hent : ∀ i j, (entL i j).baseChange ℝ z₁ = (entL (E` using `E) i j).baseChange ℝ z₂ := by`.

Introduce `i j`. Apply `hb.1` to reduce the goal to its premises. Use function extensionality and compare the values at `τ`. Use `congrFun h τ` as an intermediate fact. Simplify using `only at this ⊢`.

Rewrite using `[evaluation_baseChange_entry, evaluation_baseChange_entry, this]`. Rewrite using `[sum_sg_ent z₁, sum_sg_ent z₂]`. Simplify using `only [hent]`. Introduce `f choose w hw using fun i j => hb.2 (fun τ => f τ i j)`. Use `⟨∑ i, ∑ j, (sgL i j).baseChange ℝ (w i j), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `τ`. Simplify using `only [map_sum, evM_sg]`. Establish `hw' : ∀ i j, ev1 τ.1 (w i j) = f τ i j` using `fun i j => congrFun (hw i j) τ`. Simplify using `only [hw']`. Conclude with `(Matrix.matrix_eq_sum_single (f τ)).symm`.
-/
theorem UpperTheory.cmField_real_tensor_matrix_bijective_cmType :
    TraceType → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ), Function.Bijective (fun (z : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) (τ : Phi A) => evM τ.1 z) := by
  intro hT E _ _ _ A n
  have hb := UpperTheory.cmField_real_tensor_bijective_cmType hT A
  constructor
  · intro z₁ z₂ h
    have hent : ∀ i j, (entL i j).baseChange ℝ z₁ = (entL (E := E) i j).baseChange ℝ z₂ := by
      intro i j
      apply hb.1
      funext τ
      have := congrFun h τ
      simp only at this ⊢
      rw [evaluation_baseChange_entry, evaluation_baseChange_entry, this]
    rw [sum_sg_ent z₁, sum_sg_ent z₂]
    simp only [hent]
  · intro f
    choose w hw using fun i j => hb.2 (fun τ => f τ i j)
    refine ⟨∑ i, ∑ j, (sgL i j).baseChange ℝ (w i j), ?_⟩
    funext τ
    simp only [map_sum, evM_sg]
    have hw' : ∀ i j, ev1 τ.1 (w i j) = f τ i j := fun i j => congrFun (hw i j) τ
    simp only [hw']
    exact (Matrix.matrix_eq_sum_single (f τ)).symm
