import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.UnitaryExtension

/- English proof (translation)
Establish `hk : LinearMap.ker a ≤ LinearMap.ker b`. Introduce `x hx`. Rewrite `hx`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[← norm_eq_zero, h, hx, norm_zero]`. Set `l : LinearMap.range a →ₗ[ℂ] V` to `((LinearMap.ker a).liftQ b hk) ∘ₗ (a.quotKerEquivRange.symm : LinearMap.range a →ₗ[ℂ] _)`.

Establish `hl : ∀ x, l ⟨a x, LinearMap.mem_range_self a x⟩ = b x`. Introduce `x`. Simplify using `only [l, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[LinearMap.quotKerEquivRange_symm_apply_image]`. Simplify using the standard rewrite rules.

Set `L : LinearMap.range a →ₗᵢ[ℂ] V` to `{ toLinearMap := l norm_map' := by`. Introduce and unpack `⟨y, x, rfl⟩`. Rewrite using `[hl, h]`. Use `rfl }`. Use `⟨L.extend, fun x => ?_⟩` and prove the remaining obligations.

Use `L.extend_apply ⟨a x, LinearMap.mem_range_self a x⟩` as an intermediate fact. Rewrite using `[← hl]`. Conclude with `this`.
-/
theorem exists_isometry_comp {W V : Type} [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (a b : W →ₗ[ℂ] V)
    (h : ∀ x, ‖b x‖ = ‖a x‖) : ∃ u : V →ₗᵢ[ℂ] V, ∀ x, u (a x) = b x := by
  have hk : LinearMap.ker a ≤ LinearMap.ker b := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← norm_eq_zero, h, hx, norm_zero]
  let l : LinearMap.range a →ₗ[ℂ] V :=
    ((LinearMap.ker a).liftQ b hk) ∘ₗ (a.quotKerEquivRange.symm : LinearMap.range a →ₗ[ℂ] _)
  have hl : ∀ x, l ⟨a x, LinearMap.mem_range_self a x⟩ = b x := by
    intro x
    simp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    simp
  let L : LinearMap.range a →ₗᵢ[ℂ] V :=
    { toLinearMap := l
      norm_map' := by
        rintro ⟨y, x, rfl⟩
        rw [hl, h]; rfl }
  refine ⟨L.extend, fun x => ?_⟩
  have := L.extend_apply ⟨a x, LinearMap.mem_range_self a x⟩
  rw [← hl]
  exact this

/- English proof (translation)
Establish `key : ∀ (C : Matrix (Fin n) ι ℂ) (x : EuclideanSpace ℂ ι), inner ℂ (Matrix.toEuclideanLin C x) (Matrix.toEuclideanLin C x) = inner ℂ x (Matrix.toEuclideanLin (Cᴴ * C) x)`. Introduce `C x`. Rewrite using `[← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]`. Use `congr 1`. Simplify using `[Matrix.toLpLin_apply, Matrix.mulVec_mulVec]`.

Take `⟨u, hu⟩` from `exists_isometry_comp (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) (by`. Introduce `x`. Rewrite using `[@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ (Matrix.toEuclideanLin A x), key, key, h])`. Use `⟨Matrix.toEuclideanLin.symm u.toLinearMap, ?_, ?_⟩` and prove the remaining obligations. Apply `(Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin n) (n := Fin n)).injective ext1 x` to reduce the goal to its premises.

Apply `ext_inner_left ℂ` to reduce the goal to its premises. Introduce `y`. Establish `e : Matrix.toEuclideanLin ((Matrix.toEuclideanLin.symm u.toLinearMap)ᴴ * Matrix.toEuclideanLin.symm u.toLinearMap) x = Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap)ᴴ (Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap) x)`. Generalize the expression as in `Matrix.toEuclideanLin.symm u.toLinearMap = U`. Simplify using `[Matrix.toLpLin_apply, Matrix.mulVec_mulVec]`.

Rewrite using `[e, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]`. Simplify using `[Matrix.toLpLin_apply]`. Apply `(Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin n) (n := ι)).injective ext1 x` to reduce the goal to its premises. Establish `e : Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap * A) x = Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap) (Matrix.toEuclideanLin A x)`. Generalize the expression as in `Matrix.toEuclideanLin.symm u.toLinearMap = U`.

Simplify using `[Matrix.toLpLin_apply, Matrix.mulVec_mulVec]`. Rewrite using `[e, LinearEquiv.apply_symm_apply]`. Conclude with `hu x`.
-/
theorem exists_unitary_mul_eq {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix (Fin n) ι ℂ) (h : Aᴴ * A = Bᴴ * B) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * A = B := by
  have key : ∀ (C : Matrix (Fin n) ι ℂ) (x : EuclideanSpace ℂ ι),
      inner ℂ (Matrix.toEuclideanLin C x) (Matrix.toEuclideanLin C x)
        = inner ℂ x (Matrix.toEuclideanLin (Cᴴ * C) x) := by
    intro C x
    rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    congr 1
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  obtain ⟨u, hu⟩ := exists_isometry_comp (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) (by
    intro x
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ (Matrix.toEuclideanLin A x), key, key, h])
  refine ⟨Matrix.toEuclideanLin.symm u.toLinearMap, ?_, ?_⟩
  · apply (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin n) (n := Fin n)).injective
    ext1 x
    apply ext_inner_left ℂ
    intro y
    have e : Matrix.toEuclideanLin ((Matrix.toEuclideanLin.symm u.toLinearMap)ᴴ * Matrix.toEuclideanLin.symm u.toLinearMap) x
        = Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap)ᴴ (Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap) x) := by
      generalize Matrix.toEuclideanLin.symm u.toLinearMap = U
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    rw [e, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]
    simp [Matrix.toLpLin_apply]
  · apply (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin n) (n := ι)).injective
    ext1 x
    have e : Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap * A) x
        = Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap) (Matrix.toEuclideanLin A x) := by
      generalize Matrix.toEuclideanLin.symm u.toLinearMap = U
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    rw [e, LinearEquiv.apply_symm_apply]
    exact hu x

/- English proof (translation)
Introduce `n m E A B hE hEE hA hB hG`. Establish `hP : (1 - E)ᴴ = 1 - E` using `by rw [conjTranspose_sub, conjTranspose_one, hE]`. Establish `hPA : (1 - E) * A = 0` using `by rw [Matrix.sub_mul, Matrix.one_mul, hA, sub_self]`. Establish `hPB : (1 - E) * B = 0` using `by rw [Matrix.sub_mul, Matrix.one_mul, hB, sub_self]`. Establish `hAP : Aᴴ * (1 - E) = 0`.

Rewrite using `[← hP, ← conjTranspose_mul, hPA, conjTranspose_zero]`. Establish `hBP : Bᴴ * (1 - E) = 0`. Rewrite using `[← hP, ← conjTranspose_mul, hPB, conjTranspose_zero]`. Take `⟨U, hU, hUA⟩` from `exists_unitary_mul_eq (Matrix.fromCols A (1 - E)) (Matrix.fromCols B (1 - E)) (by`. Rewrite using `[conjTranspose_fromCols_eq_fromRows_conjTranspose, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, fromRows_mul_fromCols, hP, hG, hPA, hPB, hAP, hBP])`.

Rewrite `hUA` using `[mul_fromCols, fromCols_ext_iff]`. Take `⟨h1, h2⟩` from `hUA`. Use `⟨U, hU, ?_, h2, h1⟩` and prove the remaining obligations. Establish `hU' : U * Uᴴ = 1` using `mul_eq_one_comm.mp hU`. Establish `h3 : (1 - E) * Uᴴ = 1 - E`.

Use `congrArg conjTranspose h2` as an intermediate fact. Rewrite `this` using `[conjTranspose_mul, hP]`. Then use the resulting hypothesis. Establish `h4 : (1 - E) * U = 1 - E`. Combine the equalities or inequalities in the displayed calculation. Establish `h5 : U * (1 - E) = (1 - E) * U` using `by rw [h2, h4]`.

Rewrite `h5` using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]`. Conclude with `sub_right_injective h5`.
-/
theorem exists_unitary_of_gram_eq : ∀ (n m : ℕ) (E : Matrix (Fin n) (Fin n) ℂ) (A B : Matrix (Fin n) (Fin m) ℂ), Eᴴ = E → E * E = E → E * A = A → E * B = B → Aᴴ * A = Bᴴ * B → ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * E = E * U ∧ U * (1 - E) = 1 - E ∧ U * A = B := by
  intro n m E A B hE hEE hA hB hG
  have hP : (1 - E)ᴴ = 1 - E := by rw [conjTranspose_sub, conjTranspose_one, hE]
  have hPA : (1 - E) * A = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hA, sub_self]
  have hPB : (1 - E) * B = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hB, sub_self]
  have hAP : Aᴴ * (1 - E) = 0 := by
    rw [← hP, ← conjTranspose_mul, hPA, conjTranspose_zero]
  have hBP : Bᴴ * (1 - E) = 0 := by
    rw [← hP, ← conjTranspose_mul, hPB, conjTranspose_zero]
  obtain ⟨U, hU, hUA⟩ := exists_unitary_mul_eq (Matrix.fromCols A (1 - E))
    (Matrix.fromCols B (1 - E)) (by
      rw [conjTranspose_fromCols_eq_fromRows_conjTranspose,
        conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols,
        fromRows_mul_fromCols, hP, hG, hPA, hPB, hAP, hBP])
  rw [mul_fromCols, fromCols_ext_iff] at hUA
  obtain ⟨h1, h2⟩ := hUA
  refine ⟨U, hU, ?_, h2, h1⟩
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have h3 : (1 - E) * Uᴴ = 1 - E := by
    have := congrArg conjTranspose h2
    rwa [conjTranspose_mul, hP] at this
  have h4 : (1 - E) * U = 1 - E := by
    calc (1 - E) * U = (1 - E) * Uᴴ * U := by rw [h3]
      _ = 1 - E := by rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  have h5 : U * (1 - E) = (1 - E) * U := by rw [h2, h4]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul] at h5
  exact sub_right_injective h5

end GlobalTheory.UnitaryExtension
