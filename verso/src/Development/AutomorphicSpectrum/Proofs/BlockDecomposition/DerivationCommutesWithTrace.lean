import Mathlib
set_option backward.isDefEq.respectTransparency false
open MvPolynomial

namespace GlobalTheory.CompanionTheory.TraceDerivation

/- English proof (translation)
Introduce `K F L _ _ _ _ _ _ _ _ _ D D0 h y`. Set `b` to `Module.finBasis F L`. Set `M` to `Algebra.leftMulMatrix b y`. Set `N` to `Algebra.leftMulMatrix b (D y)`. Set `C : Matrix (Fin (Module.finrank F L)) (Fin (Module.finrank F L)) F` to `Matrix.of fun i j => b.repr (D (b j)) i`.

Establish `hmul : ∀ (z : L) (j), z * b j = ∑ i, Algebra.leftMulMatrix b z i j • b i`. Introduce `z j`. Simplify using `only [Algebra.leftMulMatrix_eq_repr_mul]`. Conclude with `(b.sum_repr _).symm`. Establish `hD : ∀ j, D (b j) = ∑ k, C k j • b k` using `fun j => (b.sum_repr _).symm`.

Establish `hsmul : ∀ (a : F) (x : L), D (a • x) = D0 a • x + a • D x`. Introduce `a x`. Rewrite using `[Algebra.smul_def, D.leibniz, h, smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ∀ j, ∑ i, (M * C) i j • b i = y * D (b j)`.

Introduce `j`. Rewrite using `[hD j, Finset.mul_sum]`. Simplify using `only [Matrix.mul_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_smul_comm, hmul y k, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Establish `h2 : ∀ j, ∑ i, (C * M) i j • b i = ∑ k, M k j • D (b k)`. Introduce `j`.

Simplify using `only [Matrix.mul_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hD k, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Establish `key : ∀ j, ∑ i, (N + M * C) i j • b i = ∑ i, (M.map D0 + C * M) i j • b i`. Introduce `j`. Establish `e` using `congrArg D (hmul y j)`. Rewrite `e` using `[D.leibniz, map_sum]`.

Simplify using `only [hsmul, Finset.sum_add_distrib, smul_eq_mul] at e`. Simplify using `only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, h1, h2, Matrix.map_apply]`. Rewrite using `[← hmul (D y) j]`. Rewrite using `[add_comm (D y * b j), mul_comm (D y), e]`. Establish `hmat : N + M * C = M.map D0 + C * M`.

Use extensionality with `i j`. Establish `: b.repr (∑ i, (N + M * C) i j • b i) i = b.repr (∑ i, (M.map D0 + C * M) i j • b i) i`. Rewrite using `[key j]`. Rewrite `this` using `[b.repr_sum_self, b.repr_sum_self]`. Conclude with `this`.

Establish `htr : Matrix.trace N = D0 (Matrix.trace M)`. Use `congrArg Matrix.trace hmat` as an intermediate fact. Rewrite `this` using `[Matrix.trace_add, Matrix.trace_add, Matrix.trace_mul_comm M C]`. Establish `h3` using `add_right_cancel this`. Rewrite using `[h3]`.

Simplify using `[Matrix.trace, map_sum]`. Use `congr 1`. Rewrite using `[Algebra.trace_eq_matrix_trace b y, Algebra.trace_eq_matrix_trace b (D y)]`. Conclude with `htr.symm`.
-/
theorem trace_map_derivation : ∀ (K F L : Type) [Field K] [CharZero K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L] [FiniteDimensional F L]
    (D : Derivation K L L) (D0 : Derivation K F F),
    (∀ x : F, D (algebraMap F L x) = algebraMap F L (D0 x)) →
    ∀ y : L, algebraMap F L (D0 (Algebra.trace F L y)) =
      algebraMap F L (Algebra.trace F L (D y)) := by
  intro K F L _ _ _ _ _ _ _ _ _ D D0 h y
  classical
  let b := Module.finBasis F L
  let M := Algebra.leftMulMatrix b y
  let N := Algebra.leftMulMatrix b (D y)
  let C : Matrix (Fin (Module.finrank F L)) (Fin (Module.finrank F L)) F :=
    Matrix.of fun i j => b.repr (D (b j)) i
  have hmul : ∀ (z : L) (j), z * b j = ∑ i, Algebra.leftMulMatrix b z i j • b i := by
    intro z j
    simp only [Algebra.leftMulMatrix_eq_repr_mul]
    exact (b.sum_repr _).symm
  have hD : ∀ j, D (b j) = ∑ k, C k j • b k := fun j => (b.sum_repr _).symm
  have hsmul : ∀ (a : F) (x : L), D (a • x) = D0 a • x + a • D x := by
    intro a x
    rw [Algebra.smul_def, D.leibniz, h, smul_eq_mul, smul_eq_mul, Algebra.smul_def,
      Algebra.smul_def]
    ring
  have h1 : ∀ j, ∑ i, (M * C) i j • b i = y * D (b j) := by
    intro j
    rw [hD j, Finset.mul_sum]
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, hmul y k, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, mul_smul]
  have h2 : ∀ j, ∑ i, (C * M) i j • b i = ∑ k, M k j • D (b k) := by
    intro j
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hD k, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, mul_smul]
  have key : ∀ j, ∑ i, (N + M * C) i j • b i = ∑ i, (M.map D0 + C * M) i j • b i := by
    intro j
    have e := congrArg D (hmul y j)
    rw [D.leibniz, map_sum] at e
    simp only [hsmul, Finset.sum_add_distrib, smul_eq_mul] at e
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, h1, h2, Matrix.map_apply]
    rw [← hmul (D y) j]
    rw [add_comm (D y * b j), mul_comm (D y), e]
  have hmat : N + M * C = M.map D0 + C * M := by
    ext i j
    have : b.repr (∑ i, (N + M * C) i j • b i) i = b.repr (∑ i, (M.map D0 + C * M) i j • b i) i := by
      rw [key j]
    rw [b.repr_sum_self, b.repr_sum_self] at this
    exact this
  have htr : Matrix.trace N = D0 (Matrix.trace M) := by
    have := congrArg Matrix.trace hmat
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_mul_comm M C] at this
    have h3 := add_right_cancel this
    rw [h3]
    simp [Matrix.trace, map_sum]
  congr 1
  rw [Algebra.trace_eq_matrix_trace b y, Algebra.trace_eq_matrix_trace b (D y)]
  exact htr.symm

end GlobalTheory.CompanionTheory.TraceDerivation
