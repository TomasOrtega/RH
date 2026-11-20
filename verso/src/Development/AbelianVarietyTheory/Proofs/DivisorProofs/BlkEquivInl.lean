import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL

noncomputable section

open Matrix

namespace GlobalTheory.LeviGA

variable {R S : Type} [CommRing R] [CommRing S] {a r : ℕ}

def blkEquiv (h : r ≤ a) : Fin r ⊕ Fin (a - r) ≃ Fin a :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem blkEquiv_inl (h : r ≤ a) (i : Fin r) : ((blkEquiv h (Sum.inl i) : Fin a) : ℕ) = i := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem blkEquiv_inr (h : r ≤ a) (i : Fin (a - r)) : ((blkEquiv h (Sum.inr i) : Fin a) : ℕ) = r + i := rfl

variable (R) in

def blkMat (h : r ≤ a) :
    Matrix (Fin r) (Fin r) R × Matrix (Fin (a - r)) (Fin (a - r)) R →* Matrix (Fin a) (Fin a) R where
  toFun p := Matrix.reindex (blkEquiv h) (blkEquiv h) (Matrix.fromBlocks p.1 0 0 p.2)
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

def blkGL (h : r ≤ a) : GL (Fin r) R × GL (Fin (a - r)) R →* GL (Fin a) R :=
  (Units.map (blkMat R h)).comp MulEquiv.prodUnits.symm.toMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blkGL_val (h : r ≤ a) (p : GL (Fin r) R × GL (Fin (a - r)) R) :
    (blkGL h p : Matrix (Fin a) (Fin a) R) =
      Matrix.reindex (blkEquiv h) (blkEquiv h) (Matrix.fromBlocks (p.1 : Matrix _ _ R) 0 0 (p.2 : Matrix _ _ R)) :=
  rfl

/- English proof (translation)
Rewrite using `[blkGL_val, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]`.
-/
theorem blkGL_apply (h : r ≤ a) (p : GL (Fin r) R × GL (Fin (a - r)) R) (i j : Fin r ⊕ Fin (a - r)) :
    (blkGL h p : Matrix (Fin a) (Fin a) R) (blkEquiv h i) (blkEquiv h j) =
      Matrix.fromBlocks (p.1 : Matrix _ _ R) 0 0 (p.2 : Matrix _ _ R) i j := by
  rw [blkGL_val, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/- English proof (translation)
Take `⟨i, rfl⟩` from `(blkEquiv h).surjective i`. Take `⟨j, rfl⟩` from `(blkEquiv h).surjective j`. Rewrite using `[blkGL_apply]`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`. Use `left`.

Simplify using the standard rewrite rules. Use `right`. Simplify using the standard rewrite rules. Use `right`. Simplify using the standard rewrite rules.

Use `left`. Simplify using the standard rewrite rules.
-/
theorem blkGL_block (h : r ≤ a) (p : GL (Fin r) R × GL (Fin (a - r)) R) (i j : Fin a) :
    ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (blkGL h p : Matrix (Fin a) (Fin a) R) i j = 0 := by
  obtain ⟨i, rfl⟩ := (blkEquiv h).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv h).surjective j
  rw [blkGL_apply]
  rcases i with i | i <;> rcases j with j | j
  · left; simp
  · right; simp
  · right; simp
  · left; simp

/- English proof (translation)
Take `⟨M, hM⟩ : ∃ M, M = (m : Matrix (Fin a) (Fin a) R).submatrix (blkEquiv h) (blkEquiv h)` from `⟨_, rfl⟩`. Establish `h12 : M.toBlocks₁₂ = 0`. Use extensionality with `i j`. Rewrite using `[Matrix.toBlocks₁₂, Matrix.of_apply, hM, Matrix.submatrix_apply, Matrix.zero_apply]`. Break down `hm (blkEquiv h (Sum.inl i)) (blkEquiv h (Sum.inr j)) with h' | h'` into its components or cases.

Rewrite `h'` using `[blkEquiv_inl, blkEquiv_inr]`. Use linear arithmetic over natural numbers and integers. Conclude with `h'`. Establish `h21 : M.toBlocks₂₁ = 0`. Use extensionality with `i j`.

Rewrite using `[Matrix.toBlocks₂₁, Matrix.of_apply, hM, Matrix.submatrix_apply, Matrix.zero_apply]`. Break down `hm (blkEquiv h (Sum.inr i)) (blkEquiv h (Sum.inl j)) with h' | h'` into its components or cases. Rewrite `h'` using `[blkEquiv_inl, blkEquiv_inr]`. Use linear arithmetic over natural numbers and integers. Conclude with `h'`.

Establish `hMb : M = Matrix.fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂` using `by conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]`. Rewrite using `[h12, h21]`. Establish `hdet : IsUnit M.det`. Rewrite using `[hM, Matrix.det_submatrix_equiv_self]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 m.isUnit`.

Rewrite `hdet` using `[hMb, Matrix.det_fromBlocks_zero₂₁]`. Establish `hA : IsUnit M.toBlocks₁₁` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hdet)`. Establish `hD : IsUnit M.toBlocks₂₂` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hdet)`. Use `⟨(hA.unit, hD.unit), Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[blkGL_val]`.

Simplify using `only [IsUnit.unit_spec]`. Rewrite using `[← hMb, hM]`. Use extensionality with `i j`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply]`.
-/
theorem exists_blkGL (h : r ≤ a) (m : GL (Fin a) R)
    (hm : ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (m : Matrix (Fin a) (Fin a) R) i j = 0) :
    ∃ p, blkGL h p = m := by
  obtain ⟨M, hM⟩ : ∃ M, M = (m : Matrix (Fin a) (Fin a) R).submatrix (blkEquiv h) (blkEquiv h) := ⟨_, rfl⟩
  have h12 : M.toBlocks₁₂ = 0 := by
    ext i j
    rw [Matrix.toBlocks₁₂, Matrix.of_apply, hM, Matrix.submatrix_apply, Matrix.zero_apply]
    rcases hm (blkEquiv h (Sum.inl i)) (blkEquiv h (Sum.inr j)) with h' | h'
    · rw [blkEquiv_inl, blkEquiv_inr] at h'; omega
    · exact h'
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    rw [Matrix.toBlocks₂₁, Matrix.of_apply, hM, Matrix.submatrix_apply, Matrix.zero_apply]
    rcases hm (blkEquiv h (Sum.inr i)) (blkEquiv h (Sum.inl j)) with h' | h'
    · rw [blkEquiv_inl, blkEquiv_inr] at h'; omega
    · exact h'
  have hMb : M = Matrix.fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [h12, h21]
  have hdet : IsUnit M.det := by
    rw [hM, Matrix.det_submatrix_equiv_self]
    exact (Matrix.isUnit_iff_isUnit_det _).1 m.isUnit
  rw [hMb, Matrix.det_fromBlocks_zero₂₁] at hdet
  have hA : IsUnit M.toBlocks₁₁ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hdet)
  have hD : IsUnit M.toBlocks₂₂ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hdet)
  refine ⟨(hA.unit, hD.unit), Units.ext ?_⟩
  rw [blkGL_val]
  simp only [IsUnit.unit_spec]
  rw [← hMb, hM]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.coe_map, blkGL_val]`. Use extensionality with `i j`. Take `⟨i, rfl⟩` from `(blkEquiv h).surjective i`. Take `⟨j, rfl⟩` from `(blkEquiv h).surjective j`.

Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.reindex_apply]`.
-/
theorem map_blkGL (h : r ≤ a) (f : R →+* S) (p : GL (Fin r) R × GL (Fin (a - r)) R) :
    Units.map f.mapMatrix.toMonoidHom (blkGL h p) =
      blkGL h (Units.map f.mapMatrix.toMonoidHom p.1, Units.map f.mapMatrix.toMonoidHom p.2) := by
  apply Units.ext
  simp only [Units.coe_map, blkGL_val]
  ext i j
  obtain ⟨i, rfl⟩ := (blkEquiv h).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv h).surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.reindex_apply]

end GlobalTheory.LeviGA

end
