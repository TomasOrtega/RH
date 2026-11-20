import Mathlib

open Matrix

namespace GlobalTheory

/- English proof (translation)
Use `set D : Matrix (Fin d) (Fin d) E := Matrix.of fun k m => Algebra.trace E E' (w k * w m) with hD`. Use `set C : Matrix (Fin d) (Fin d) E := w.toMatrix v with hC`. Use `set Λ : Matrix (Fin d × Fin n) (Fin d × Fin n) E := Matrix.of fun p q => Algebra.leftMulMatrix w (H p.2 q.2) p.1 q.1 with hΛ`. Establish `htr : ∀ k (y : E'), Algebra.trace E E' (w k * y) = ∑ m, D k m * w.repr y m`. Introduce `k y`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[w.sum_repr y]`. Use `_ = ∑ m, D k m * w.repr y m := by`. Simplify using `only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul, hD, of_apply]`. Conclude with `Finset.sum_congr rfl fun m _ => mul_comm _ _`.

Establish `hrep : ∀ (x y : E') m, w.repr (x * y) m = ∑ s, Algebra.leftMulMatrix w x m s * w.repr y s`. Introduce `x y m`. Use `congrFun (Algebra.leftMulMatrix_mulVec_repr w x y) m` as an intermediate fact. Rewrite using `[← this]`. Simplify using `[Matrix.mulVec, dotProduct]`.

Establish `hDC : D * C = Matrix.of fun k l => Algebra.trace E E' (w k * v l)`. Use extensionality with `k l`. Simplify using `[Matrix.mul_apply, htr, hC, Module.Basis.toMatrix_apply]`. Establish `hM : (Matrix.of fun (p q : Fin d × Fin n) => Algebra.trace E E' (w p.1 * H p.2 q.2 * v q.1)) = blockDiagonal (fun _ : Fin n => D) * Λ * blockDiagonal (fun _ : Fin n => C)`. Use extensionality with `⟨k, i⟩ ⟨l, j⟩`.

Simplify using `only [Matrix.mul_apply, Fintype.sum_prod_type, blockDiagonal_apply, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, of_apply, hΛ]`. Rewrite using `[mul_assoc, htr]`. Simplify using `only [hrep, hC, Module.Basis.toMatrix_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.

Establish `hΛdet : Λ.det = Algebra.norm E H.det`. Set `bt` to `w.smulTower (Pi.basisFun E' (Fin n))`. Establish `hmat : LinearMap.toMatrix bt bt ((Matrix.toLin' H).restrictScalars E) = Λ`. Use extensionality with `⟨k, i⟩ ⟨l, j⟩`. Simplify using `[LinearMap.toMatrix_apply, bt, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr, hΛ, Algebra.leftMulMatrix_eq_repr_mul, Matrix.mulVec, dotProduct, Pi.single_apply]`.

Rewrite using `[mul_comm]`. Rewrite using `[← hmat, LinearMap.det_toMatrix, LinearMap.det_restrictScalars, LinearMap.det_toLin']`. Rewrite using `[hM, det_mul, det_mul, det_blockDiagonal, det_blockDiagonal, hΛdet, ← hDC, det_mul]`. Simplify using `[Finset.prod_const, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_traceGram_blockMatrix {E E' : Type} [Field E] [Field E'] [Algebra E E'] [FiniteDimensional E E'] {d n : ℕ}
    (w : Module.Basis (Fin d) E E') (H : Matrix (Fin n) (Fin n) E') (v : Fin d → E') :
    (Matrix.of fun (p q : Fin d × Fin n) => Algebra.trace E E' (w p.1 * H p.2 q.2 * v q.1)).det
      = (Matrix.of fun k l => Algebra.trace E E' (w k * v l)).det ^ n * Algebra.norm E H.det := by
  classical
  set D : Matrix (Fin d) (Fin d) E := Matrix.of fun k m => Algebra.trace E E' (w k * w m) with hD
  set C : Matrix (Fin d) (Fin d) E := w.toMatrix v with hC
  set Λ : Matrix (Fin d × Fin n) (Fin d × Fin n) E :=
    Matrix.of fun p q => Algebra.leftMulMatrix w (H p.2 q.2) p.1 q.1 with hΛ

  have htr : ∀ k (y : E'), Algebra.trace E E' (w k * y) = ∑ m, D k m * w.repr y m := by
    intro k y
    calc Algebra.trace E E' (w k * y) = Algebra.trace E E' (w k * ∑ m, w.repr y m • w m) := by
          rw [w.sum_repr y]
      _ = ∑ m, D k m * w.repr y m := by
          simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul, hD, of_apply]
          exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have hrep : ∀ (x y : E') m, w.repr (x * y) m = ∑ s, Algebra.leftMulMatrix w x m s * w.repr y s := by
    intro x y m
    have := congrFun (Algebra.leftMulMatrix_mulVec_repr w x y) m
    rw [← this]; simp [Matrix.mulVec, dotProduct]
  have hDC : D * C = Matrix.of fun k l => Algebra.trace E E' (w k * v l) := by
    ext k l
    simp [Matrix.mul_apply, htr, hC, Module.Basis.toMatrix_apply]
  have hM : (Matrix.of fun (p q : Fin d × Fin n) => Algebra.trace E E' (w p.1 * H p.2 q.2 * v q.1))
      = blockDiagonal (fun _ : Fin n => D) * Λ * blockDiagonal (fun _ : Fin n => C) := by
    ext ⟨k, i⟩ ⟨l, j⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, blockDiagonal_apply, ite_mul, mul_ite, zero_mul,
      mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, of_apply, hΛ]
    rw [mul_assoc, htr]
    simp only [hrep, hC, Module.Basis.toMatrix_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hΛdet : Λ.det = Algebra.norm E H.det := by
    let bt := w.smulTower (Pi.basisFun E' (Fin n))
    have hmat : LinearMap.toMatrix bt bt ((Matrix.toLin' H).restrictScalars E) = Λ := by
      ext ⟨k, i⟩ ⟨l, j⟩
      simp [LinearMap.toMatrix_apply, bt, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr, hΛ,
        Algebra.leftMulMatrix_eq_repr_mul, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [mul_comm]
    rw [← hmat, LinearMap.det_toMatrix, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  rw [hM, det_mul, det_mul, det_blockDiagonal, det_blockDiagonal, hΛdet, ← hDC, det_mul]
  simp [Finset.prod_const, mul_pow]
  ring

end GlobalTheory
