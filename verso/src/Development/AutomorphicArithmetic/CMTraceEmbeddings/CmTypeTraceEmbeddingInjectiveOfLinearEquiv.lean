import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.OrientEv
import Development.AutomorphicArithmetic.CMTraceEmbeddings.CmFieldRealTensorBijectiveCmType

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed UpperTheory.Gal.W2.Seed.Ori
open scoped TensorProduct

/- English proof (translation)
Introduce `hT E _ _ _ A n V _ _ β z z' h`. Establish `hb` using `(UpperTheory.cmField_real_tensor_bijective_cmType hT A).1`. Use `set B : V →ₗ[ℚ] (Fin n → E) := (β : V →ₗ[ℚ] (Fin n → E)) with hBdef`. Establish `key : ∀ j (y : ℝ ⊗[ℚ] V) (τ : Phi A), Th (fun τ : Phi A => τ.1) B y (τ, j) = ev1 τ.1 ((LinearMap.proj j ∘ₗ B).baseChange ℝ y)`. Introduce `j y τ`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r w`. Rewrite using `[Th_tmul, LinearMap.baseChange_tmul, realTensorEvalAlgHom_tmul]`. Both sides reduce to the same expression.

Consider the case `add a b ha hb'`. Rewrite using `[map_add, Pi.add_apply, ha, hb', map_add, map_add]`. Establish `hj : ∀ j, (LinearMap.proj j ∘ₗ B).baseChange ℝ z = (LinearMap.proj j ∘ₗ B).baseChange ℝ z'`. Introduce `j`. Apply `hb` to reduce the goal to its premises.

Use function extensionality and compare the values at `τ`. Simplify using `only`. Rewrite using `[← key, ← key, h]`. Establish `hsum : ∀ y : ℝ ⊗[ℚ] (Fin n → E), y = ∑ j, (LinearMap.single ℚ (fun _ : Fin n => E) j).baseChange ℝ ((LinearMap.proj j : (Fin n → E) →ₗ[ℚ] E).baseChange ℝ y)`. Introduce `y`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r v`. Simplify using `only [LinearMap.baseChange_tmul, ← TensorProduct.tmul_sum]`. Use `congr 1`.

Simplify using `[Finset.univ_sum_single v]`. Consider the case `add a b ha hb' => conv_lhs => rw [ha, hb']`. Simplify using `only [map_add, ← Finset.sum_add_distrib]`. Establish `hc : ∀ j (y : ℝ ⊗[ℚ] V), (LinearMap.proj j : (Fin n → E) →ₗ[ℚ] E).baseChange ℝ (B.baseChange ℝ y) = (LinearMap.proj j ∘ₗ B).baseChange ℝ y`. Introduce `j y`.

Rewrite using `[LinearMap.baseChange_comp]`. Both sides reduce to the same expression. Establish `hB : B.baseChange ℝ z = B.baseChange ℝ z'`. Rewrite using `[hsum (B.baseChange ℝ z), hsum (B.baseChange ℝ z')]`. Simplify using `only [hc, hj]`.

Establish `hid : ((β.symm : (Fin n → E) →ₗ[ℚ] V).baseChange ℝ).comp (B.baseChange ℝ) = LinearMap.id`. Rewrite using `[← LinearMap.baseChange_comp, hBdef, LinearEquiv.symm_comp, LinearMap.baseChange_id]`. Establish `hl : ∀ x, ((β.symm : (Fin n → E) →ₗ[ℚ] V).baseChange ℝ) (B.baseChange ℝ x) = x` using `fun x => LinearMap.congr_fun hid x`. Rewrite using `[← hl z, ← hl z', hB]`.
-/
theorem UpperTheory.cmType_trace_embedding_injective_of_linearEquiv :
    TraceType → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (β : V ≃ₗ[ℚ] (Fin n → E)), Function.Injective (Th (fun τ : Phi A => τ.1) (β : V →ₗ[ℚ] (Fin n → E))) := by
  intro hT E _ _ _ A n V _ _ β z z' h
  have hb := (UpperTheory.cmField_real_tensor_bijective_cmType hT A).1
  set B : V →ₗ[ℚ] (Fin n → E) := (β : V →ₗ[ℚ] (Fin n → E)) with hBdef
  have key : ∀ j (y : ℝ ⊗[ℚ] V) (τ : Phi A), Th (fun τ : Phi A => τ.1) B y (τ, j) =
      ev1 τ.1 ((LinearMap.proj j ∘ₗ B).baseChange ℝ y) := by
    intro j y τ
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r w =>
      rw [Th_tmul, LinearMap.baseChange_tmul, realTensorEvalAlgHom_tmul]
      rfl
    | add a b ha hb' =>
      rw [map_add, Pi.add_apply, ha, hb', map_add, map_add]
  have hj : ∀ j, (LinearMap.proj j ∘ₗ B).baseChange ℝ z = (LinearMap.proj j ∘ₗ B).baseChange ℝ z' := by
    intro j
    apply hb
    funext τ
    simp only
    rw [← key, ← key, h]
  have hsum : ∀ y : ℝ ⊗[ℚ] (Fin n → E), y = ∑ j, (LinearMap.single ℚ (fun _ : Fin n => E) j).baseChange ℝ
      ((LinearMap.proj j : (Fin n → E) →ₗ[ℚ] E).baseChange ℝ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r v =>
      simp only [LinearMap.baseChange_tmul, ← TensorProduct.tmul_sum]
      congr 1
      simp [Finset.univ_sum_single v]
    | add a b ha hb' =>
      conv_lhs => rw [ha, hb']
      simp only [map_add, ← Finset.sum_add_distrib]
  have hc : ∀ j (y : ℝ ⊗[ℚ] V), (LinearMap.proj j : (Fin n → E) →ₗ[ℚ] E).baseChange ℝ (B.baseChange ℝ y) =
      (LinearMap.proj j ∘ₗ B).baseChange ℝ y := by
    intro j y
    rw [LinearMap.baseChange_comp]
    rfl
  have hB : B.baseChange ℝ z = B.baseChange ℝ z' := by
    rw [hsum (B.baseChange ℝ z), hsum (B.baseChange ℝ z')]
    simp only [hc, hj]
  have hid : ((β.symm : (Fin n → E) →ₗ[ℚ] V).baseChange ℝ).comp (B.baseChange ℝ) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hBdef, LinearEquiv.symm_comp, LinearMap.baseChange_id]
  have hl : ∀ x, ((β.symm : (Fin n → E) →ₗ[ℚ] V).baseChange ℝ) (B.baseChange ℝ x) = x :=
    fun x => LinearMap.congr_fun hid x
  rw [← hl z, ← hl z', hB]
