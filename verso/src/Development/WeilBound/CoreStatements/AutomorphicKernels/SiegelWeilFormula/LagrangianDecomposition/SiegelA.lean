import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.BlockIndexInrLast

noncomputable section

open Matrix

namespace PositivityTheory.SiegelWeilFormula.Ald

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem block_index_inl_embedded {N n : ℕ} (h : n + 1 = N) (a : Fin n) : eB h (Sum.inl (em0 h a)) = Sum.inl (Sum.inl a) :=
  PositivityTheory.SiegelWeilFormula.Ald.eB_map h (Sum.inl a)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem block_index_inr_embedded {N n : ℕ} (h : n + 1 = N) (a : Fin n) : eB h (Sum.inr (em0 h a)) = Sum.inl (Sum.inr a) :=
  PositivityTheory.SiegelWeilFormula.Ald.eB_map h (Sum.inr a)

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Prove the first alternative. Extract witnesses or component facts from the available result. Prove the second alternative. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem blk_fromRows {R : Type*} [CommRing R] {N n : ℕ} (h : n + 1 = N) (P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (A : Matrix (Fin n) (Fin n) R)
    (hP : P * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin n) R) =
      Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin n) R) * A) :
    blk h P 1 * Matrix.fromRows (1 : Matrix (Fin N) (Fin N) R) (0 : Matrix (Fin N) (Fin N) R) =
      Matrix.fromRows (1 : Matrix (Fin N) (Fin N) R) (0 : Matrix (Fin N) (Fin N) R) *
        (Matrix.fromBlocks A 0 0 1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R).submatrix (eI h) (eI h) := by
  have hA : ∀ i j, P (Sum.inl i) (Sum.inl j) = A i j := by
    intro i j
    have := congrFun (congrFun hP (Sum.inl i)) j
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] using this
  have hB : ∀ i j, P (Sum.inr i) (Sum.inl j) = 0 := by
    intro i j
    have := congrFun (congrFun hP (Sum.inr i)) j
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] using this
  have key : ∀ c : Fin N, c = PositivityTheory.SiegelWeilFormula.Ald.i0 h ∨ ∃ j, c = PositivityTheory.SiegelWeilFormula.Ald.em0 h j := by
    intro c
    by_cases hc : c = PositivityTheory.SiegelWeilFormula.Ald.i0 h
    · exact Or.inl hc
    · obtain ⟨j, rfl⟩ := (PositivityTheory.SiegelWeilFormula.Ald.ne_last_iff_mem_range h c).1 hc
      exact Or.inr ⟨j, rfl⟩
  ext u c
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type]
  rcases u with a | a <;> rcases key a with rfl | ⟨i, rfl⟩ <;> rcases key c with rfl | ⟨j, rfl⟩ <;>
    simp [Matrix.one_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.block_index_inl_embedded,
      PositivityTheory.SiegelWeilFormula.Ald.block_index_inr_embedded, PositivityTheory.SiegelWeilFormula.Ald.block_index_inl_last, PositivityTheory.SiegelWeilFormula.Ald.block_index_inr_last,
      PositivityTheory.SiegelWeilFormula.Ald.index_embedded_equiv, PositivityTheory.SiegelWeilFormula.Ald.index_last_equiv, hA, hB]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem det_blkA {R : Type*} [CommRing R] {N n : ℕ} (h : n + 1 = N) (A : Matrix (Fin n) (Fin n) R) :
    ((Matrix.fromBlocks A 0 0 1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R).submatrix (eI h) (eI h)).det = A.det := by
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

end PositivityTheory.SiegelWeilFormula.Ald

end
