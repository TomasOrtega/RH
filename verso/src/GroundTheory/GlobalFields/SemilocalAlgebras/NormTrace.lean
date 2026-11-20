import Mathlib
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite

namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module Matrix

noncomputable section

namespace SemiLocal

/- English proof (translation)
Set `_ : LinearOrder α` to `LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective`. Rewrite using `[(blockTriangular_blockDiagonal' d).det_fintype]`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Establish `: (blockDiagonal' d).toSquareBlock Sigma.fst k = (d k).submatrix (Equiv.sigmaSubtype k) (Equiv.sigmaSubtype k)`. Use extensionality with `⟨⟨i, a⟩, hi⟩ ⟨⟨j, b⟩, hj⟩`.

Simplify using `only at hi hj`. Substitute `hi hj` using the available equality. Simplify using `[toSquareBlock_def, Equiv.sigmaSubtype]`. Rewrite using `[this, det_submatrix_equiv_self]`.
-/
theorem det_blockDiagonal' {α : Type*} [Fintype α] [DecidableEq α] {m : α → Type*}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {R : Type*} [CommRing R]
    (d : ∀ i, Matrix (m i) (m i) R) : (blockDiagonal' d).det = ∏ k, (d k).det := by
  classical
  let _ : LinearOrder α := LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  rw [(blockTriangular_blockDiagonal' d).det_fintype]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  have : (blockDiagonal' d).toSquareBlock Sigma.fst k =
      (d k).submatrix (Equiv.sigmaSubtype k) (Equiv.sigmaSubtype k) := by
    ext ⟨⟨i, a⟩, hi⟩ ⟨⟨j, b⟩, hj⟩
    dsimp only at hi hj
    subst hi hj
    simp [toSquareBlock_def, Equiv.sigmaSubtype]
  rw [this, det_submatrix_equiv_self]

variable {R : Type*} [Field R] {ι : Type*} [Fintype ι] {S : ι → Type*} [∀ i, CommRing (S i)]
  [∀ i, Algebra R (S i)] [∀ i, Module.Finite R (S i)]

omit [∀ i, Module.Finite R (S i)] in
/- English proof (translation)
Use extensionality with `⟨i, k⟩ ⟨j, l⟩`. Rewrite using `[Algebra.leftMulMatrix_eq_repr_mul, blockDiagonal'_apply', Pi.basis_repr, Pi.basis_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[Algebra.leftMulMatrix_eq_repr_mul]`.

Simplify using `[h]`.
-/
theorem leftMulMatrix_pi [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    [∀ i, DecidableEq (κ i)] (b : ∀ i, Basis (κ i) R (S i)) (x : ∀ i, S i) :
    Algebra.leftMulMatrix (Pi.basis b) x =
      blockDiagonal' fun i ↦ Algebra.leftMulMatrix (b i) (x i) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [Algebra.leftMulMatrix_eq_repr_mul, blockDiagonal'_apply', Pi.basis_repr, Pi.basis_apply]
  by_cases h : i = j
  · subst h
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  · simp [h]

/- English proof (translation)
Set `b` to `fun i ↦ Module.finBasis R (S i)`. Rewrite using `[Algebra.norm_eq_matrix_det (Pi.basis b), leftMulMatrix_pi, det_blockDiagonal']`. Conclude with `Finset.prod_congr rfl fun i _ ↦ (Algebra.norm_eq_matrix_det (b i) (x i)).symm`.
-/
theorem norm_pi (x : ∀ i, S i) : Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  classical
  let b := fun i ↦ Module.finBasis R (S i)
  rw [Algebra.norm_eq_matrix_det (Pi.basis b), leftMulMatrix_pi, det_blockDiagonal']
  exact Finset.prod_congr rfl fun i _ ↦ (Algebra.norm_eq_matrix_det (b i) (x i)).symm

/- English proof (translation)
Set `b` to `fun i ↦ Module.finBasis R (S i)`. Rewrite using `[Algebra.trace_eq_matrix_trace (Pi.basis b), leftMulMatrix_pi, trace_blockDiagonal']`. Conclude with `Finset.sum_congr rfl fun i _ ↦ (Algebra.trace_eq_matrix_trace (b i) (x i)).symm`.
-/
theorem trace_pi (x : ∀ i, S i) :
    Algebra.trace R (∀ i, S i) x = ∑ i, Algebra.trace R (S i) (x i) := by
  classical
  let b := fun i ↦ Module.finBasis R (S i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), leftMulMatrix_pi, trace_blockDiagonal']
  exact Finset.sum_congr rfl fun i _ ↦ (Algebra.trace_eq_matrix_trace (b i) (x i)).symm

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))

/- English proof (translation)
Rewrite using `[Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange]`.
-/
theorem norm_one_tmul (x : L) :
    Algebra.norm (v.adicCompletion K) ((1 : v.adicCompletion K) ⊗ₜ[K] x) =
      algebraMap K (v.adicCompletion K) (Algebra.norm K x) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange]

/- English proof (translation)
Rewrite using `[Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]`.
-/
theorem trace_one_tmul (x : L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        ((1 : v.adicCompletion K) ⊗ₜ[K] x) =
      algebraMap K (v.adicCompletion K) (Algebra.trace K L x) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange]

/- English proof (translation)
Rewrite using `[← norm_one_tmul, ← Algebra.norm_eq_of_algEquiv (tensorEquiv L v), tensorEquiv_one_tmul, norm_pi]`. Both sides reduce to the same expression.
-/
theorem algebraMap_norm_eq_prod (x : L) :
    algebraMap K (v.adicCompletion K) (Algebra.norm K x) =
      ∏ w : PlacesOver L v,
        Algebra.norm (v.adicCompletion K) (algebraMap L (w.1.adicCompletion L) x) := by
  rw [← norm_one_tmul, ← Algebra.norm_eq_of_algEquiv (tensorEquiv L v), tensorEquiv_one_tmul,
    norm_pi]
  rfl

/- English proof (translation)
Rewrite using `[← trace_one_tmul, ← Algebra.trace_eq_of_algEquiv (tensorEquiv L v), tensorEquiv_one_tmul, trace_pi]`. Both sides reduce to the same expression.
-/
theorem algebraMap_trace_eq_sum (x : L) :
    algebraMap K (v.adicCompletion K) (Algebra.trace K L x) =
      ∑ w : PlacesOver L v, Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L)
        (algebraMap L (w.1.adicCompletion L) x) := by
  rw [← trace_one_tmul, ← Algebra.trace_eq_of_algEquiv (tensorEquiv L v), tensorEquiv_one_tmul,
    trace_pi]
  rfl

end SemiLocal

end

end GroundTheory.Global
