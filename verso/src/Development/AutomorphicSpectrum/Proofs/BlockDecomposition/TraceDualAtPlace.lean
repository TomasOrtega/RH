import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.AlmostGoodOf

noncomputable section

namespace GlobalTheory.CompanionTheory.Gunr.TraceDual

open NumberField IsDedekindDomain PositivityTheory.SiegelWeilFormula.Gunr HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct

section Abstract

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] {d : ℕ}

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem repr_mul_mem (O : Subring K) (b : Module.Basis (Fin d) K A)
    (hc : ∀ i j k, b.repr (b i * b j) k ∈ O) {x y : A}
    (hx : ∀ k, b.repr x k ∈ O) (hy : ∀ k, b.repr y k ∈ O) (k : Fin d) :
    b.repr (x * y) k ∈ O := by
  have hxy : x * y = ∑ i, ∑ j, (b.repr x i * b.repr y j) • (b i * b j) := by
    conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm]
  have h : b.repr (x * y) k = ∑ i, ∑ j, b.repr x i * b.repr y j * b.repr (b i * b j) k := by
    rw [hxy]
    simp [map_sum, Finsupp.finset_sum_apply]
  rw [h]
  exact O.sum_mem fun i _ => O.sum_mem fun j _ => O.mul_mem (O.mul_mem (hx i) (hy j)) (hc i j k)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem repr_basis_mem (O : Subring K) (b : Module.Basis (Fin d) K A) (j k : Fin d) :
    b.repr (b j) k ∈ O := by
  rw [b.repr_self, Finsupp.single_apply]
  split_ifs
  · exact O.one_mem
  · exact O.zero_mem

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem trace_mem (O : Subring K) (b : Module.Basis (Fin d) K A)
    (hc : ∀ i j k, b.repr (b i * b j) k ∈ O) {x : A} (hx : ∀ k, b.repr x k ∈ O) :
    Algebra.trace K A x ∈ O := by
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine O.sum_mem fun i _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  exact repr_mul_mem O b hc hx (repr_basis_mem O b i) i

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem adjugate_mem (O : Subring K) (M : Matrix (Fin d) (Fin d) K) (hM : ∀ i j, M i j ∈ O) (i j : Fin d) :
    M.adjugate i j ∈ O := by
  let N : Matrix (Fin d) (Fin d) O := Matrix.of fun i j => ⟨M i j, hM i j⟩
  have hN : O.subtype.mapMatrix N = M := by
    ext i j
    rfl
  rw [← hN, ← RingHom.map_adjugate]
  exact (N.adjugate i j).2

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem dual_iff (O : Subring K) (b : Module.Basis (Fin d) K A)
    (hc : ∀ i j k, b.repr (b i * b j) k ∈ O) (u : K) (huO : u ∈ O)
    (hu : u * (Algebra.traceMatrix K b).det = 1) (a : A) :
    (∀ y : A, (∀ k, b.repr y k ∈ O) → Algebra.trace K A (a * y) ∈ O) ↔ ∀ k, b.repr a k ∈ O := by
  constructor
  · intro h k
    set M := Algebra.traceMatrix K b with hMdef
    have hMij : ∀ i j, M i j = Algebra.trace K A (b i * b j) := fun i j => by
      simp [hMdef, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    have hMO : ∀ i j, M i j ∈ O := fun i j => by
      rw [hMij]
      exact trace_mem O b hc (hc i j)
    let c : Fin d → K := fun i => b.repr a i
    let t : Fin d → K := fun j => Algebra.trace K A (a * b j)
    have ht : Matrix.vecMul c M = t := by
      funext j
      have ha : a * b j = ∑ i, c i • (b i * b j) := by
        conv_lhs => rw [← b.sum_repr a, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc]
      simp only [t, Matrix.vecMul, dotProduct, hMij]
      rw [ha, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul]
    have hc' : M.det • c = Matrix.vecMul t M.adjugate := by
      rw [← ht, Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
    have hk : b.repr a k = u * ∑ j, t j * M.adjugate j k := by
      have h1 := congrFun hc' k
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct] at h1
      rw [← h1, ← mul_assoc, hu, one_mul]
    rw [hk]
    refine O.mul_mem huO (O.sum_mem fun j _ => O.mul_mem ?_ (adjugate_mem O M hMO j k))
    exact h _ (repr_basis_mem O b j)
  · intro ha y hy
    exact trace_mem O b hc (repr_mul_mem O b hc ha hy)

end Abstract

section Base

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {K : Type*} [Field K] [Algebra F K] {d : ℕ}

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem trace_one_tmul [FiniteDimensional F E] (e : E) :
    Algebra.trace K (K ⊗[F] E) ((1 : K) ⊗ₜ[F] e) = algebraMap F K (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem traceMatrix_base (bs : Module.Basis (Fin d) F E) :
    Algebra.traceMatrix K (Algebra.TensorProduct.basis K bs) =
      (Algebra.traceMatrix F bs).map (algebraMap F K) := by
  haveI : FiniteDimensional F E := Module.Basis.finiteDimensional_of_finite bs
  ext i j
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.map_apply,
    Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem det_traceMatrix_base (bs : Module.Basis (Fin d) F E) :
    (Algebra.traceMatrix K (Algebra.TensorProduct.basis K bs)).det =
      algebraMap F K (Algebra.discr F (⇑bs)) := by
  rw [traceMatrix_base, Algebra.discr_def, RingHom.map_det]
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem repr_base (bs : Module.Basis (Fin d) F E) (i j k : Fin d) :
    (Algebra.TensorProduct.basis K bs).repr
        (Algebra.TensorProduct.basis K bs i * Algebra.TensorProduct.basis K bs j) k =
      algebraMap F K (bs.repr (bs i * bs j) k) := by
  simp [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.basis_repr_tmul]

end Base

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Prove the first alternative. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem traceDualAt : TraceDualAt := by
  intro F E _ _ _ _ _ σ _ d bs v hv a
  let O : Subring (Fv F v) := (v.adicCompletionIntegers F).toSubring
  have hc : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) bs).repr
      (Algebra.TensorProduct.basis (Fv F v) bs i * Algebra.TensorProduct.basis (Fv F v) bs j) k ∈ O := by
    intro i j k
    rw [repr_base]
    refine hv _ ?_
    simp only [basisSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inl (Or.inl ⟨(i, j, k), rfl⟩))
  have hD : Algebra.discr F (⇑bs) ≠ 0 := by
    exact Algebra.discr_not_zero_of_basis F bs
  have hu : algebraMap F (Fv F v) (Algebra.discr F (⇑bs))⁻¹ ∈ O := by
    refine hv _ ?_
    simp [basisSet]
  have h1 : algebraMap F (Fv F v) (Algebra.discr F (⇑bs))⁻¹ *
      (Algebra.traceMatrix (Fv F v) (Algebra.TensorProduct.basis (Fv F v) bs)).det = 1 := by
    rw [det_traceMatrix_base, ← map_mul, inv_mul_cancel₀ hD, map_one]
  have key := dual_iff O (Algebra.TensorProduct.basis (Fv F v) bs) hc _ hu h1 a
  exact key

end GlobalTheory.CompanionTheory.Gunr.TraceDual

end
