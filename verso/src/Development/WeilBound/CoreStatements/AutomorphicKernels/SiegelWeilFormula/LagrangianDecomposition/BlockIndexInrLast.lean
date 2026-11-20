import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Em0Injective

noncomputable section

open Matrix

namespace PositivityTheory.SiegelWeilFormula.Ald

def eI {N n : ℕ} (h : n + 1 = N) : Fin N ≃ Fin n ⊕ Fin 1 := (finCongr h.symm).trans finSumFinEquiv.symm

def eB {N n : ℕ} (h : n + 1 = N) : Fin N ⊕ Fin N ≃ (Fin n ⊕ Fin n) ⊕ (Fin 1 ⊕ Fin 1) :=
  (Equiv.sumCongr (eI h) (eI h)).trans (Equiv.sumSumSumComm _ _ _ _)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem index_embedded_equiv {N n : ℕ} (h : n + 1 = N) (i : Fin n) : eI h (em0 h i) = Sum.inl i := by
  have hi : finCongr h.symm (PositivityTheory.SiegelWeilFormula.Ald.em0 h i) = Fin.castAdd 1 i := Fin.ext rfl
  rw [PositivityTheory.SiegelWeilFormula.Ald.eI, Equiv.trans_apply, hi, finSumFinEquiv_symm_apply_castAdd]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem index_last_equiv {N n : ℕ} (h : n + 1 = N) : eI h (i0 h) = Sum.inr 0 := by
  have hi : finCongr h.symm (PositivityTheory.SiegelWeilFormula.Ald.i0 h) = Fin.natAdd n (0 : Fin 1) := Fin.ext (by simp [PositivityTheory.SiegelWeilFormula.Ald.i0])
  rw [PositivityTheory.SiegelWeilFormula.Ald.eI, Equiv.trans_apply, hi, finSumFinEquiv_symm_apply_natAdd]

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem eB_map {N n : ℕ} (h : n + 1 = N) (u : Fin n ⊕ Fin n) :
    eB h (Sum.map (em0 h) (em0 h) u) = Sum.inl u := by
  rcases u with a | a
  · show Equiv.sumSumSumComm _ _ _ _ (Sum.inl (PositivityTheory.SiegelWeilFormula.Ald.eI h (PositivityTheory.SiegelWeilFormula.Ald.em0 h a))) = _
    rw [PositivityTheory.SiegelWeilFormula.Ald.index_embedded_equiv]
    rfl
  · show Equiv.sumSumSumComm _ _ _ _ (Sum.inr (PositivityTheory.SiegelWeilFormula.Ald.eI h (PositivityTheory.SiegelWeilFormula.Ald.em0 h a))) = _
    rw [PositivityTheory.SiegelWeilFormula.Ald.index_embedded_equiv]
    rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem block_index_inl_last {N n : ℕ} (h : n + 1 = N) : eB h (Sum.inl (i0 h)) = Sum.inr (Sum.inl 0) := by
  show Equiv.sumSumSumComm _ _ _ _ (Sum.inl (PositivityTheory.SiegelWeilFormula.Ald.eI h (PositivityTheory.SiegelWeilFormula.Ald.i0 h))) = _
  rw [PositivityTheory.SiegelWeilFormula.Ald.index_last_equiv]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem block_index_inr_last {N n : ℕ} (h : n + 1 = N) : eB h (Sum.inr (i0 h)) = Sum.inr (Sum.inr 0) := by
  show Equiv.sumSumSumComm _ _ _ _ (Sum.inr (PositivityTheory.SiegelWeilFormula.Ald.eI h (PositivityTheory.SiegelWeilFormula.Ald.i0 h))) = _
  rw [PositivityTheory.SiegelWeilFormula.Ald.index_last_equiv]
  rfl

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Prove the second alternative. Extract witnesses or component facts from the available result.

Prove the first alternative. Apply the first step, then apply the next step to every resulting obligation. Prove the first alternative. Prove the second alternative. Prove the first alternative.

Prove the second alternative.
-/
theorem idx_cases {N n : ℕ} (h : n + 1 = N) (u : Fin N ⊕ Fin N) :
    (∃ u', u = Sum.map (em0 h) (em0 h) u') ∨ u = Sum.inl (i0 h) ∨ u = Sum.inr (i0 h) := by
  have key : ∀ i : Fin N, (∃ j, i = PositivityTheory.SiegelWeilFormula.Ald.em0 h j) ∨ i = PositivityTheory.SiegelWeilFormula.Ald.i0 h := by
    intro i
    by_cases hi : i = PositivityTheory.SiegelWeilFormula.Ald.i0 h
    · exact Or.inr hi
    · obtain ⟨j, rfl⟩ := (PositivityTheory.SiegelWeilFormula.Ald.ne_last_iff_mem_range h i).1 hi
      exact Or.inl ⟨j, rfl⟩
  rcases u with i | i <;> rcases key i with ⟨j, rfl⟩ | rfl
  · exact Or.inl ⟨Sum.inl j, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl ⟨Sum.inr j, rfl⟩
  · exact Or.inr (Or.inr rfl)

/- English proof (translation)
Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Supply the required witnesses or components.
-/
theorem eB_out {N n : ℕ} (h : n + 1 = N) (u : Fin N ⊕ Fin N) (hu : u ∈ ({Sum.inl (i0 h), Sum.inr (i0 h)} : Set (Fin N ⊕ Fin N))) :
    ∃ p, eB h u = Sum.inr p := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl
  · exact ⟨_, PositivityTheory.SiegelWeilFormula.Ald.block_index_inl_last h⟩
  · exact ⟨_, PositivityTheory.SiegelWeilFormula.Ald.block_index_inr_last h⟩

variable {R : Type*}

def blk [Zero R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) R :=
  (Matrix.fromBlocks M 0 0 P).submatrix (eB h) (eB h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blk_apply [Zero R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) (u v : Fin N ⊕ Fin N) :
    blk h M P u v = Matrix.fromBlocks M 0 0 P (eB h u) (eB h v) := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem blk_map_apply [Zero R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) (u v : Fin n ⊕ Fin n) :
    blk h M P (Sum.map (em0 h) (em0 h) u) (Sum.map (em0 h) (em0 h) v) = M u v := by
  rw [PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.eB_map, PositivityTheory.SiegelWeilFormula.Ald.eB_map]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem blk_sub [Zero R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) :
    (blk h M P).submatrix (Sum.map (em0 h) (em0 h)) (Sum.map (em0 h) (em0 h)) = M :=
  Matrix.ext fun u v => PositivityTheory.SiegelWeilFormula.Ald.blk_map_apply h M P u v

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem blk_mul [NonUnitalNonAssocSemiring R] {N n : ℕ} (h : n + 1 = N) (M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P P' : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) : blk h M P * blk h M' P' = blk h (M * M') (P * P') := by
  simp [PositivityTheory.SiegelWeilFormula.Ald.blk, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem blk_one [Semiring R] {N n : ℕ} (h : n + 1 = N) : blk h (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) 1 = 1 := by
  simp [PositivityTheory.SiegelWeilFormula.Ald.blk, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem blk_transpose [Zero R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) : (blk h M P)ᵀ = blk h Mᵀ Pᵀ := by
  simp [PositivityTheory.SiegelWeilFormula.Ald.blk, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem blk_map [Zero R] {S : Type*} [Zero S] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) (f : R → S) (hf : f 0 = 0) :
    (blk h M P).map f = blk h (M.map f) (P.map f) := by
  ext u v
  rw [Matrix.map_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply]
  rcases PositivityTheory.SiegelWeilFormula.Ald.eB h u with a | a <;> rcases PositivityTheory.SiegelWeilFormula.Ald.eB h v with b | b <;>
    simp [hf]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem blk_conjTranspose [AddMonoid R] [StarAddMonoid R] {N n : ℕ} (h : n + 1 = N)
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) :
    (blk h M P)ᴴ = blk h Mᴴ Pᴴ := by
  simp [PositivityTheory.SiegelWeilFormula.Ald.blk, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. By extensionality, compare the relevant components.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem blk_inj [Zero R] {N n : ℕ} (h : n + 1 = N) {M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R}
    {P P' : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R} (e : blk h M P = blk h M' P') : M = M' ∧ P = P' := by
  constructor
  · ext i j
    have hij := congrFun (congrFun e ((PositivityTheory.SiegelWeilFormula.Ald.eB h).symm (Sum.inl i)))
      ((PositivityTheory.SiegelWeilFormula.Ald.eB h).symm (Sum.inl j))
    simpa [PositivityTheory.SiegelWeilFormula.Ald.blk_apply] using hij
  · ext i j
    have hij := congrFun (congrFun e ((PositivityTheory.SiegelWeilFormula.Ald.eB h).symm (Sum.inr i)))
      ((PositivityTheory.SiegelWeilFormula.Ald.eB h).symm (Sum.inr j))
    simpa [PositivityTheory.SiegelWeilFormula.Ald.blk_apply] using hij

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem blk_eq_one_iff [Semiring R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    blk h M 1 = 1 ↔ M = 1 := by
  constructor
  · intro e
    exact (PositivityTheory.SiegelWeilFormula.Ald.blk_inj h (e.trans (PositivityTheory.SiegelWeilFormula.Ald.blk_one h).symm)).1
  · rintro rfl
    exact PositivityTheory.SiegelWeilFormula.Ald.blk_one h

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eq_blk [Semiring R] {N n : ℕ} (h : n + 1 = N) (X : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) R)
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (hin : X.submatrix (Sum.map (em0 h) (em0 h)) (Sum.map (em0 h) (em0 h)) = M)
    (hout : ∀ u ∈ ({Sum.inl (i0 h), Sum.inr (i0 h)} : Set (Fin N ⊕ Fin N)), ∀ v,
      X u v = (1 : Matrix _ _ R) u v ∧ X v u = (1 : Matrix _ _ R) v u) : X = blk h M 1 := by
  have hrow : ∀ u v, u ∈ ({Sum.inl (PositivityTheory.SiegelWeilFormula.Ald.i0 h), Sum.inr (PositivityTheory.SiegelWeilFormula.Ald.i0 h)} : Set (Fin N ⊕ Fin N)) →
      X u v = PositivityTheory.SiegelWeilFormula.Ald.blk h M 1 u v := by
    intro u v hu
    obtain ⟨p, hp⟩ := PositivityTheory.SiegelWeilFormula.Ald.eB_out h u hu
    rw [(hout u hu v).1, ← PositivityTheory.SiegelWeilFormula.Ald.blk_one h, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, hp]
    rcases PositivityTheory.SiegelWeilFormula.Ald.eB h v with q | q <;> rfl
  have hcol : ∀ u v, v ∈ ({Sum.inl (PositivityTheory.SiegelWeilFormula.Ald.i0 h), Sum.inr (PositivityTheory.SiegelWeilFormula.Ald.i0 h)} : Set (Fin N ⊕ Fin N)) →
      X u v = PositivityTheory.SiegelWeilFormula.Ald.blk h M 1 u v := by
    intro u v hv
    obtain ⟨p, hp⟩ := PositivityTheory.SiegelWeilFormula.Ald.eB_out h v hv
    rw [(hout v hv u).2, ← PositivityTheory.SiegelWeilFormula.Ald.blk_one h, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, hp]
    rcases PositivityTheory.SiegelWeilFormula.Ald.eB h u with q | q <;> rfl
  ext u v
  rcases PositivityTheory.SiegelWeilFormula.Ald.idx_cases h u with ⟨u', rfl⟩ | hu | hu
  · rcases PositivityTheory.SiegelWeilFormula.Ald.idx_cases h v with ⟨v', rfl⟩ | hv | hv
    · rw [PositivityTheory.SiegelWeilFormula.Ald.blk_map_apply]
      exact congrFun (congrFun hin u') v'
    · exact hcol _ _ (by simp [hv])
    · exact hcol _ _ (by simp [hv])
  · exact hrow _ _ (by simp [hu])
  · exact hrow _ _ (by simp [hu])

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Prove the second alternative. Extract witnesses or component facts from the available result. Prove the first alternative.

By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem jepsR_blk [Semiring R] {N n : ℕ} (h : n + 1 = N) (c : R) :
    (Matrix.fromBlocks 0 1 (c • 1) 0 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) R) =
      blk h (Matrix.fromBlocks 0 1 (c • 1) 0) (Matrix.fromBlocks 0 1 (c • 1) 0) := by
  have hne : ∀ a : Fin n, PositivityTheory.SiegelWeilFormula.Ald.em0 h a ≠ PositivityTheory.SiegelWeilFormula.Ald.i0 h := fun a =>
    (PositivityTheory.SiegelWeilFormula.Ald.ne_last_iff_mem_range h _).2 ⟨a, rfl⟩
  have hne' : ∀ a : Fin n, PositivityTheory.SiegelWeilFormula.Ald.i0 h ≠ PositivityTheory.SiegelWeilFormula.Ald.em0 h a := fun a => (hne a).symm
  have hl : ∀ a, PositivityTheory.SiegelWeilFormula.Ald.eB h (Sum.inl (PositivityTheory.SiegelWeilFormula.Ald.em0 h a)) = Sum.inl (Sum.inl a) :=
    fun a => PositivityTheory.SiegelWeilFormula.Ald.eB_map h (Sum.inl a)
  have hr : ∀ a, PositivityTheory.SiegelWeilFormula.Ald.eB h (Sum.inr (PositivityTheory.SiegelWeilFormula.Ald.em0 h a)) = Sum.inl (Sum.inr a) :=
    fun a => PositivityTheory.SiegelWeilFormula.Ald.eB_map h (Sum.inr a)
  have key : ∀ i : Fin N, (∃ j, i = PositivityTheory.SiegelWeilFormula.Ald.em0 h j) ∨ i = PositivityTheory.SiegelWeilFormula.Ald.i0 h := by
    intro i
    by_cases hi : i = PositivityTheory.SiegelWeilFormula.Ald.i0 h
    · exact Or.inr hi
    · obtain ⟨j, rfl⟩ := (PositivityTheory.SiegelWeilFormula.Ald.ne_last_iff_mem_range h i).1 hi
      exact Or.inl ⟨j, rfl⟩
  ext u v
  rcases u with i | i <;> rcases v with j | j <;> rcases key i with ⟨i, rfl⟩ | rfl <;>
    rcases key j with ⟨j, rfl⟩ | rfl <;>
    simp [PositivityTheory.SiegelWeilFormula.Ald.blk_apply, hl, hr, PositivityTheory.SiegelWeilFormula.Ald.block_index_inl_last, PositivityTheory.SiegelWeilFormula.Ald.block_index_inr_last, Matrix.one_apply, hne, hne',
      (PositivityTheory.SiegelWeilFormula.Ald.em0_injective h).eq_iff]

end PositivityTheory.SiegelWeilFormula.Ald

end
