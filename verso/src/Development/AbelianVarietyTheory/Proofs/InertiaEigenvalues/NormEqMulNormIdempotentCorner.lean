import Mathlib
open NumberField IsDedekindDomain TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply the first step, then apply the next step to every resulting obligation. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_scale_idem_add_compl {K A : Type} [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] (ψ : A →ₐ[K] K) (e : A) (he : ψ e = 1)
    (hea : ∀ a, e * a = algebraMap K A (ψ a) * e) (c : K) :
    Algebra.norm K (algebraMap K A c * e + (1 - e)) = c := by
  classical
  let b := Module.Free.chooseBasis K A
  rw [Algebra.norm_apply, ← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b (Algebra.lmul K A (algebraMap K A c * e + (1 - e))) =
      1 + Matrix.replicateCol Unit (fun i => (c - 1) * b.repr e i) *
        Matrix.replicateRow Unit (fun j => ψ (b j)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change b.repr ((algebraMap K A c * e + (1 - e)) * b j) i = _
    have h1 : (algebraMap K A c * e + (1 - e)) * b j = b j + ((c - 1) * ψ (b j)) • e := by
      have := hea (b j)
      rw [Algebra.smul_def, map_mul, map_sub, map_one]
      linear_combination (algebraMap K A c - 1) * this
    simp only [h1, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Module.Basis.repr_self, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, smul_eq_mul]
    rw [Finsupp.single_apply]
    congr 1
    · split_ifs with h h' h' <;> first | rfl | (exfalso; exact h' h.symm) | (exfalso; exact h h'.symm)
    · ring
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hs : ∑ j, ψ (b j) * ((c - 1) * b.repr e j) = (c - 1) * ψ e := by
    conv_rhs => rw [← b.sum_repr e]
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]; ring
  rw [dotProduct, hs, he]; ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem norm_eq_mul_norm_idem_corner : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (ψ : A →ₐ[K] K) (e : A), ψ e = 1 → (∀ a, e * a = algebraMap K A (ψ a) * e) → ∀ a : A, Algebra.norm K a = ψ a * Algebra.norm K (e + (1 - e) * a) := by
  intro K A _ _ _ _ ψ e he hea a
  have hee : e * e = e := by rw [hea e, he, map_one, one_mul]
  have hid : a = (e + (1 - e) * a) * (algebraMap K A (ψ a) * e + (1 - e)) := by
    have h1 := hea a
    linear_combination (-(algebraMap K A (ψ a) - algebraMap K A (ψ a) * a + a - 1)) * hee + h1
  conv_lhs => rw [hid]
  rw [map_mul, norm_scale_idem_add_compl ψ e he hea, mul_comm]

end GlobalTheory
