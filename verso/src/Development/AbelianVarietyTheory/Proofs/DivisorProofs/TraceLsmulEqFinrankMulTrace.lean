import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis R Λ`. Set `e` to `Module.Free.chooseBasis Λ M`. Rewrite using `[LinearMap.trace_eq_matrix_trace R (b.smulTower e), Algebra.trace_eq_matrix_trace b, Module.finrank_eq_card_chooseBasisIndex]`. Simplify using `only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, LinearMap.toMatrix_apply, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr, Algebra.leftMulMatrix_eq_repr_mul]`. Establish `h : ∀ i k, (b.repr ((e.repr (((Algebra.lsmul R R M) a) (b i • e k))) k)) i = (b.repr (a * b i)) i`.

Introduce `i k`. Use `show (b.repr ((e.repr (a • (b i • e k))) k)) i = _`. Rewrite using `[smul_smul, LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]`. Simplify using `only [h]`. Rewrite using `[Finset.sum_comm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.
-/
theorem trace_lsmul_free_eq_finrank_mul_trace (R Λ M : Type) [CommRing R] [Nontrivial R] [CommRing Λ] [Nontrivial Λ] [Algebra R Λ] [Module.Free R Λ] [Module.Finite R Λ] [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower R Λ M] [Module.Free Λ M] [Module.Finite Λ M] (a : Λ) :
    LinearMap.trace R M (Algebra.lsmul R R M a) = (Module.finrank Λ M : R) * Algebra.trace R Λ a := by
  classical
  let b := Module.Free.chooseBasis R Λ
  let e := Module.Free.chooseBasis Λ M
  rw [LinearMap.trace_eq_matrix_trace R (b.smulTower e), Algebra.trace_eq_matrix_trace b,
    Module.finrank_eq_card_chooseBasisIndex]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, LinearMap.toMatrix_apply,
    Module.Basis.smulTower_apply, Module.Basis.smulTower_repr, Algebra.leftMulMatrix_eq_repr_mul]
  have h : ∀ i k, (b.repr ((e.repr (((Algebra.lsmul R R M) a) (b i • e k))) k)) i = (b.repr (a * b i)) i := by
    intro i k
    show (b.repr ((e.repr (a • (b i • e k))) k)) i = _
    rw [smul_smul, LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  simp only [h]
  rw [Finset.sum_comm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end GlobalTheory
