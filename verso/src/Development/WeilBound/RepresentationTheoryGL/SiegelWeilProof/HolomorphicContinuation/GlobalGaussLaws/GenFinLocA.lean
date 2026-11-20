import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRedField

noncomputable section

set_option linter.unusedSectionVars false

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

def bf (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  M.submatrix finSumFinEquiv finSumFinEquiv

/- English proof (translation)
Unfold `bf`. Conclude with `(Matrix.submatrix_mul_equiv M N _ _ _).symm`.
-/
theorem bf_mul (M N : Matrix (Fin (n + n)) (Fin (n + n)) R) : bf (M * N) = bf M * bf N := by
  unfold bf; exact (Matrix.submatrix_mul_equiv M N _ _ _).symm

/- English proof (translation)
Unfold `bf GlobalTheory.StdUnn.blk4`. Simplify using `[Matrix.submatrix_submatrix]`.
-/
theorem block_matrix_to_fromBlocks (a b c d : Matrix (Fin n) (Fin n) R) : bf (GlobalTheory.StdUnn.blk4 a b c d) = fromBlocks a b c d := by
  unfold bf GlobalTheory.StdUnn.blk4; simp [Matrix.submatrix_submatrix]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blkDm_eq (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : blkDm M = (bf M).toBlocks₂₂ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bf_map (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : bf (M.map f) = (bf M).map f := rfl

/- English proof (translation)
The claim follows from `Matrix.submatrix_one_equiv _`.
-/
theorem bf_one : bf (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := Matrix.submatrix_one_equiv _

/- English proof (translation)
Introduce `M N h`. Use extensionality with `i j`. Use `congrFun (congrFun h (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)` as an intermediate fact. Simplify `this` using `[bf]`.
-/
theorem bf_injective : Function.Injective (bf : Matrix (Fin (n + n)) (Fin (n + n)) R → _) := by
  intro M N h
  ext i j
  have := congrFun (congrFun h (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  simpa [bf] using this

/- English proof (translation)
The claim follows from `bf_injective (by rw [block_matrix_to_fromBlocks, bf_one, fromBlocks_one])`.
-/
theorem block_matrix_one : GlobalTheory.StdUnn.blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 :=
  bf_injective (by rw [block_matrix_to_fromBlocks, bf_one, fromBlocks_one])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blkDm_map (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : (blkDm M).map f = blkDm (M.map f) := rfl

/- English proof (translation)
Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem det_map (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) : f M.det = (M.map f).det := by
  rw [RingHom.map_det]; rfl

/- English proof (translation)
The claim follows from `bf_injective (by rw [bf_map, block_matrix_to_fromBlocks, block_matrix_to_fromBlocks, fromBlocks_map])`.
-/
theorem block_matrix_map (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (GlobalTheory.StdUnn.blk4 a b c d).map f = GlobalTheory.StdUnn.blk4 (a.map f) (b.map f) (c.map f) (d.map f) :=
  bf_injective (by rw [bf_map, block_matrix_to_fromBlocks, block_matrix_to_fromBlocks, fromBlocks_map])

/- English proof (translation)
Apply the tactic sequence `ext i j; simp only [eI, map_apply, diagonal_apply]; split_ifs <;> simp`.
-/
theorem eI_map (f : R →+* S) (I : Finset (Fin n)) : (eI I : Matrix (Fin n) (Fin n) R).map f = eI I := by
  ext i j; simp only [eI, map_apply, diagonal_apply]; split_ifs <;> simp

/- English proof (translation)
Unfold `wIm`. Rewrite using `[block_matrix_map]`. Simplify using `[Matrix.map_sub, Matrix.map_one, Matrix.map_neg, eI_map]`.
-/
theorem wIm_map (f : R →+* S) (I : Finset (Fin n)) : (wIm I : Matrix (Fin (n + n)) (Fin (n + n)) R).map f = wIm I := by
  unfold wIm; rw [block_matrix_map]; simp [Matrix.map_sub, Matrix.map_one, Matrix.map_neg, eI_map]

/- English proof (translation)
Unfold `J2`. Rewrite using `[block_matrix_map]`. Simplify using `[Matrix.map_one, Matrix.map_neg]`.
-/
theorem standard_symplectic_matrix_map (f : R →+* S) : (J2 R n).map f = J2 S n := by
  unfold J2; rw [block_matrix_map]; simp [Matrix.map_one, Matrix.map_neg]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, hf]`.
-/
theorem cT_map (σ : R →+* R) (σ' : S →+* S) (f : R →+* S) (hf : ∀ x, f (σ x) = σ' (f x)) {m p : Type}
    (M : Matrix m p R) : (Formalism.UG.cT σ M).map f = Formalism.UG.cT σ' (M.map f) := by
  ext i j; simp [Formalism.UG.cT, hf]

/- English proof (translation)
Assume the negation of the conclusion as `hz`. Take `⟨𝔫, h𝔫, hz𝔫⟩` from `Ideal.exists_le_maximal (Ideal.span {z}) (by rwa [Ne, Ideal.span_singleton_eq_top])`. Establish `hz' : z ∈ 𝔫` using `hz𝔫 (Ideal.subset_span rfl)`. Break down `horb 𝔫 h𝔫 with rfl | rfl` into its components or cases. Conclude with `h1 hz'`.

Conclude with `h2 hz'`.
-/
theorem isUnit_of (σ : R →+* R) (𝔪 : Ideal R) (horb : ∀ 𝔫 : Ideal R, 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap σ)
    (z : R) (h1 : z ∉ 𝔪) (h2 : σ z ∉ 𝔪) : IsUnit z := by
  by_contra hz
  obtain ⟨𝔫, h𝔫, hz𝔫⟩ := Ideal.exists_le_maximal (Ideal.span {z}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hz' : z ∈ 𝔫 := hz𝔫 (Ideal.subset_span rfl)
  rcases horb 𝔫 h𝔫 with rfl | rfl
  · exact h1 hz'
  · exact h2 hz'

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
