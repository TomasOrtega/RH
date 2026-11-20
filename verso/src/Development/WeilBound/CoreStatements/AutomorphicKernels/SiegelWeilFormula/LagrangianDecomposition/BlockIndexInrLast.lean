import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Em0Injective

noncomputable section

open Matrix

namespace PositivityTheory.SiegelWeilFormula.Ald

def eI {N n : ℕ} (h : n + 1 = N) : Fin N ≃ Fin n ⊕ Fin 1 := (finCongr h.symm).trans finSumFinEquiv.symm

def eB {N n : ℕ} (h : n + 1 = N) : Fin N ⊕ Fin N ≃ (Fin n ⊕ Fin n) ⊕ (Fin 1 ⊕ Fin 1) :=
  (Equiv.sumCongr (eI h) (eI h)).trans (Equiv.sumSumSumComm _ _ _ _)

/- English proof (translation)
Establish `hi : finCongr h.symm (PositivityTheory.SiegelWeilFormula.Ald.em0 h i) = Fin.castAdd 1 i` using `Fin.ext rfl`. Rewrite using `[PositivityTheory.SiegelWeilFormula.Ald.eI, Equiv.trans_apply, hi, finSumFinEquiv_symm_apply_castAdd]`.
-/
theorem index_embedded_equiv {N n : ℕ} (h : n + 1 = N) (i : Fin n) : eI h (em0 h i) = Sum.inl i := by
  have hi : finCongr h.symm (PositivityTheory.SiegelWeilFormula.Ald.em0 h i) = Fin.castAdd 1 i := Fin.ext rfl
  rw [PositivityTheory.SiegelWeilFormula.Ald.eI, Equiv.trans_apply, hi, finSumFinEquiv_symm_apply_castAdd]

/- English proof (translation)
Establish `hi : finCongr h.symm (PositivityTheory.SiegelWeilFormula.Ald.i0 h) = Fin.natAdd n (0 : Fin 1)` using `Fin.ext (by simp [PositivityTheory.SiegelWeilFormula.Ald.i0])`. Rewrite using `[PositivityTheory.SiegelWeilFormula.Ald.eI, Equiv.trans_apply, hi, finSumFinEquiv_symm_apply_natAdd]`.
-/
theorem index_last_equiv {N n : ℕ} (h : n + 1 = N) : eI h (i0 h) = Sum.inr 0 := by
  have hi : finCongr h.symm (PositivityTheory.SiegelWeilFormula.Ald.i0 h) = Fin.natAdd n (0 : Fin 1) := Fin.ext (by simp [PositivityTheory.SiegelWeilFormula.Ald.i0])
  rw [PositivityTheory.SiegelWeilFormula.Ald.eI, Equiv.trans_apply, hi, finSumFinEquiv_symm_apply_natAdd]

/- English proof (translation)
Break down `u with a | a` into its components or cases. Use `show Equiv.sumSumSumComm _ _ _ _ (Sum.inl (PositivityTheory.SiegelWeilFormula.Ald.eI h (PositivityTheory.SiegelWeilFormula.Ald.em0 h a))) = _`. Rewrite using `[PositivityTheory.SiegelWeilFormula.Ald.index_embedded_equiv]`. Both sides reduce to the same expression. Use `show Equiv.sumSumSumComm _ _ _ _ (Sum.inr (PositivityTheory.SiegelWeilFormula.Ald.eI h (PositivityTheory.SiegelWeilFormula.Ald.em0 h a))) = _`.

Rewrite using `[PositivityTheory.SiegelWeilFormula.Ald.index_embedded_equiv]`. Both sides reduce to the same expression.
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
Use `show Equiv.sumSumSumComm _ _ _ _ (Sum.inl (PositivityTheory.SiegelWeilFormula.Ald.eI h (PositivityTheory.SiegelWeilFormula.Ald.i0 h))) = _`. Rewrite using `[PositivityTheory.SiegelWeilFormula.Ald.index_last_equiv]`. Both sides reduce to the same expression.
-/
theorem block_index_inl_last {N n : ℕ} (h : n + 1 = N) : eB h (Sum.inl (i0 h)) = Sum.inr (Sum.inl 0) := by
  show Equiv.sumSumSumComm _ _ _ _ (Sum.inl (PositivityTheory.SiegelWeilFormula.Ald.eI h (PositivityTheory.SiegelWeilFormula.Ald.i0 h))) = _
  rw [PositivityTheory.SiegelWeilFormula.Ald.index_last_equiv]
  rfl

/- English proof (translation)
Use `show Equiv.sumSumSumComm _ _ _ _ (Sum.inr (PositivityTheory.SiegelWeilFormula.Ald.eI h (PositivityTheory.SiegelWeilFormula.Ald.i0 h))) = _`. Rewrite using `[PositivityTheory.SiegelWeilFormula.Ald.index_last_equiv]`. Both sides reduce to the same expression.
-/
theorem block_index_inr_last {N n : ℕ} (h : n + 1 = N) : eB h (Sum.inr (i0 h)) = Sum.inr (Sum.inr 0) := by
  show Equiv.sumSumSumComm _ _ _ _ (Sum.inr (PositivityTheory.SiegelWeilFormula.Ald.eI h (PositivityTheory.SiegelWeilFormula.Ald.i0 h))) = _
  rw [PositivityTheory.SiegelWeilFormula.Ald.index_last_equiv]
  rfl

/- English proof (translation)
Establish `key : ∀ i : Fin N, (∃ j, i = PositivityTheory.SiegelWeilFormula.Ald.em0 h j) ∨ i = PositivityTheory.SiegelWeilFormula.Ald.i0 h`. Introduce `i`. Distinguish the cases in `hi : i = PositivityTheory.SiegelWeilFormula.Ald.i0 h`. Conclude with `Or.inr hi`. Take `⟨j, rfl⟩` from `(PositivityTheory.SiegelWeilFormula.Ald.ne_last_iff_mem_range h i).1 hi`.

Conclude with `Or.inl ⟨j, rfl⟩`. Apply the tactic sequence `rcases u with i | i <;> rcases key i with ⟨j, rfl⟩ | rfl`. Conclude with `Or.inl ⟨Sum.inl j, rfl⟩`. Conclude with `Or.inr (Or.inl rfl)`. Conclude with `Or.inl ⟨Sum.inr j, rfl⟩`.

Conclude with `Or.inr (Or.inr rfl)`.
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
Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu`. Break down `hu with rfl | rfl` into its components or cases. Conclude with `⟨_, PositivityTheory.SiegelWeilFormula.Ald.block_index_inl_last h⟩`. Conclude with `⟨_, PositivityTheory.SiegelWeilFormula.Ald.block_index_inr_last h⟩`.
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
Rewrite using `[PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.eB_map, PositivityTheory.SiegelWeilFormula.Ald.eB_map]`. Both sides reduce to the same expression.
-/
theorem blk_map_apply [Zero R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) (u v : Fin n ⊕ Fin n) :
    blk h M P (Sum.map (em0 h) (em0 h) u) (Sum.map (em0 h) (em0 h) v) = M u v := by
  rw [PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.eB_map, PositivityTheory.SiegelWeilFormula.Ald.eB_map]
  rfl

/- English proof (translation)
The claim follows from `Matrix.ext fun u v => PositivityTheory.SiegelWeilFormula.Ald.blk_map_apply h M P u v`.
-/
theorem blk_sub [Zero R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) :
    (blk h M P).submatrix (Sum.map (em0 h) (em0 h)) (Sum.map (em0 h) (em0 h)) = M :=
  Matrix.ext fun u v => PositivityTheory.SiegelWeilFormula.Ald.blk_map_apply h M P u v

/- English proof (translation)
Simplify using `[PositivityTheory.SiegelWeilFormula.Ald.blk, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`.
-/
theorem blk_mul [NonUnitalNonAssocSemiring R] {N n : ℕ} (h : n + 1 = N) (M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P P' : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) : blk h M P * blk h M' P' = blk h (M * M') (P * P') := by
  simp [PositivityTheory.SiegelWeilFormula.Ald.blk, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

/- English proof (translation)
Simplify using `[PositivityTheory.SiegelWeilFormula.Ald.blk, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]`.
-/
theorem blk_one [Semiring R] {N n : ℕ} (h : n + 1 = N) : blk h (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) 1 = 1 := by
  simp [PositivityTheory.SiegelWeilFormula.Ald.blk, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

/- English proof (translation)
Simplify using `[PositivityTheory.SiegelWeilFormula.Ald.blk, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]`.
-/
theorem blk_transpose [Zero R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) : (blk h M P)ᵀ = blk h Mᵀ Pᵀ := by
  simp [PositivityTheory.SiegelWeilFormula.Ald.blk, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

/- English proof (translation)
Use extensionality with `u v`. Rewrite using `[Matrix.map_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply]`. Apply the tactic sequence `rcases PositivityTheory.SiegelWeilFormula.Ald.eB h u with a | a <;> rcases PositivityTheory.SiegelWeilFormula.Ald.eB h v with b | b <;>`. Simplify using `[hf]`.
-/
theorem blk_map [Zero R] {S : Type*} [Zero S] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) (f : R → S) (hf : f 0 = 0) :
    (blk h M P).map f = blk h (M.map f) (P.map f) := by
  ext u v
  rw [Matrix.map_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply]
  rcases PositivityTheory.SiegelWeilFormula.Ald.eB h u with a | a <;> rcases PositivityTheory.SiegelWeilFormula.Ald.eB h v with b | b <;>
    simp [hf]

/- English proof (translation)
Simplify using `[PositivityTheory.SiegelWeilFormula.Ald.blk, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]`.
-/
theorem blk_conjTranspose [AddMonoid R] [StarAddMonoid R] {N n : ℕ} (h : n + 1 = N)
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) :
    (blk h M P)ᴴ = blk h Mᴴ Pᴴ := by
  simp [PositivityTheory.SiegelWeilFormula.Ald.blk, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use extensionality with `i j`. Establish `hij` using `congrFun (congrFun e ((PositivityTheory.SiegelWeilFormula.Ald.eB h).symm (Sum.inl i))) ((PositivityTheory.SiegelWeilFormula.Ald.eB h).symm (Sum.inl j))`. Simplify `hij` using `[PositivityTheory.SiegelWeilFormula.Ald.blk_apply]`. Use extensionality with `i j`.

Establish `hij` using `congrFun (congrFun e ((PositivityTheory.SiegelWeilFormula.Ald.eB h).symm (Sum.inr i))) ((PositivityTheory.SiegelWeilFormula.Ald.eB h).symm (Sum.inr j))`. Simplify `hij` using `[PositivityTheory.SiegelWeilFormula.Ald.blk_apply]`.
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
Prove the components needed by the constructor for the conclusion. Introduce `e`. Conclude with `(PositivityTheory.SiegelWeilFormula.Ald.blk_inj h (e.trans (PositivityTheory.SiegelWeilFormula.Ald.blk_one h).symm)).1`. Introduce and unpack `rfl`. Conclude with `PositivityTheory.SiegelWeilFormula.Ald.blk_one h`.
-/
theorem blk_eq_one_iff [Semiring R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    blk h M 1 = 1 ↔ M = 1 := by
  constructor
  · intro e
    exact (PositivityTheory.SiegelWeilFormula.Ald.blk_inj h (e.trans (PositivityTheory.SiegelWeilFormula.Ald.blk_one h).symm)).1
  · rintro rfl
    exact PositivityTheory.SiegelWeilFormula.Ald.blk_one h

/- English proof (translation)
Establish `hrow : ∀ u v, u ∈ ({Sum.inl (PositivityTheory.SiegelWeilFormula.Ald.i0 h), Sum.inr (PositivityTheory.SiegelWeilFormula.Ald.i0 h)} : Set (Fin N ⊕ Fin N)) → X u v = PositivityTheory.SiegelWeilFormula.Ald.blk h M 1 u v`. Introduce `u v hu`. Take `⟨p, hp⟩` from `PositivityTheory.SiegelWeilFormula.Ald.eB_out h u hu`. Rewrite using `[(hout u hu v).1, ← PositivityTheory.SiegelWeilFormula.Ald.blk_one h, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, hp]`. Apply the tactic sequence `rcases PositivityTheory.SiegelWeilFormula.Ald.eB h v with q | q <;> rfl`.

Establish `hcol : ∀ u v, v ∈ ({Sum.inl (PositivityTheory.SiegelWeilFormula.Ald.i0 h), Sum.inr (PositivityTheory.SiegelWeilFormula.Ald.i0 h)} : Set (Fin N ⊕ Fin N)) → X u v = PositivityTheory.SiegelWeilFormula.Ald.blk h M 1 u v`. Introduce `u v hv`. Take `⟨p, hp⟩` from `PositivityTheory.SiegelWeilFormula.Ald.eB_out h v hv`. Rewrite using `[(hout v hv u).2, ← PositivityTheory.SiegelWeilFormula.Ald.blk_one h, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, hp]`. Apply the tactic sequence `rcases PositivityTheory.SiegelWeilFormula.Ald.eB h u with q | q <;> rfl`.

Use extensionality with `u v`. Break down `PositivityTheory.SiegelWeilFormula.Ald.idx_cases h u with ⟨u', rfl⟩ | hu | hu` into its components or cases. Break down `PositivityTheory.SiegelWeilFormula.Ald.idx_cases h v with ⟨v', rfl⟩ | hv | hv` into its components or cases. Rewrite using `[PositivityTheory.SiegelWeilFormula.Ald.blk_map_apply]`. Conclude with `congrFun (congrFun hin u') v'`.

Conclude with `hcol _ _ (by simp [hv])`. Conclude with `hcol _ _ (by simp [hv])`. Conclude with `hrow _ _ (by simp [hu])`. Conclude with `hrow _ _ (by simp [hu])`.
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
Establish `hne : ∀ a : Fin n, PositivityTheory.SiegelWeilFormula.Ald.em0 h a ≠ PositivityTheory.SiegelWeilFormula.Ald.i0 h` using `fun a => (PositivityTheory.SiegelWeilFormula.Ald.ne_last_iff_mem_range h _).2 ⟨a, rfl⟩`. Establish `hne' : ∀ a : Fin n, PositivityTheory.SiegelWeilFormula.Ald.i0 h ≠ PositivityTheory.SiegelWeilFormula.Ald.em0 h a` using `fun a => (hne a).symm`. Establish `hl : ∀ a, PositivityTheory.SiegelWeilFormula.Ald.eB h (Sum.inl (PositivityTheory.SiegelWeilFormula.Ald.em0 h a)) = Sum.inl (Sum.inl a)` using `fun a => PositivityTheory.SiegelWeilFormula.Ald.eB_map h (Sum.inl a)`. Establish `hr : ∀ a, PositivityTheory.SiegelWeilFormula.Ald.eB h (Sum.inr (PositivityTheory.SiegelWeilFormula.Ald.em0 h a)) = Sum.inl (Sum.inr a)` using `fun a => PositivityTheory.SiegelWeilFormula.Ald.eB_map h (Sum.inr a)`. Establish `key : ∀ i : Fin N, (∃ j, i = PositivityTheory.SiegelWeilFormula.Ald.em0 h j) ∨ i = PositivityTheory.SiegelWeilFormula.Ald.i0 h`.

Introduce `i`. Distinguish the cases in `hi : i = PositivityTheory.SiegelWeilFormula.Ald.i0 h`. Conclude with `Or.inr hi`. Take `⟨j, rfl⟩` from `(PositivityTheory.SiegelWeilFormula.Ald.ne_last_iff_mem_range h i).1 hi`. Conclude with `Or.inl ⟨j, rfl⟩`.

Use extensionality with `u v`. Apply the tactic sequence `rcases u with i | i <;> rcases v with j | j <;> rcases key i with ⟨i, rfl⟩ | rfl <;>`. Apply the tactic sequence `rcases key j with ⟨j, rfl⟩ | rfl <;>`. Simplify using `[PositivityTheory.SiegelWeilFormula.Ald.blk_apply, hl, hr, PositivityTheory.SiegelWeilFormula.Ald.block_index_inl_last, PositivityTheory.SiegelWeilFormula.Ald.block_index_inr_last, Matrix.one_apply, hne, hne', (PositivityTheory.SiegelWeilFormula.Ald.em0_injective h).eq_iff]`.
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
