import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroupA

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace TransM

variable {k r : ℕ}

def pK (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val < r + k

instance (k r : ℕ) : DecidablePred (pK k r) := fun i => inferInstanceAs (Decidable (r ≤ i.val ∧ i.val < r + k))

def Qm (a : Matrix {i // pK k r i} {i // pK k r i} ℂ) (b : Matrix {i // ¬ pK k r i} {i // ¬ pK k r i} ℂ) :
    Mat k r :=
  Matrix.reindex (Equiv.sumCompl (pK k r)) (Equiv.sumCompl (pK k r)) (fromBlocks a 0 0 b)

/- English proof (translation)
Simplify using `only [Qm, Matrix.reindex_apply, Matrix.submatrix_apply]`. Apply the tactic sequence `by_cases hi : pK k r i <;> by_cases hj : pK k r j <;>`. Simplify using `[hi, hj, Equiv.sumCompl_symm_apply_of_pos, Equiv.sumCompl_symm_apply_of_neg]`.
-/
theorem Qm_apply (a : Matrix {i // pK k r i} {i // pK k r i} ℂ) (b : Matrix {i // ¬ pK k r i} {i // ¬ pK k r i} ℂ)
    (i j : Fin (2 * r + k + 1)) :
    Qm a b i j = if hi : pK k r i then (if hj : pK k r j then a ⟨i, hi⟩ ⟨j, hj⟩ else 0)
      else (if hj : pK k r j then 0 else b ⟨i, hi⟩ ⟨j, hj⟩) := by
  simp only [Qm, Matrix.reindex_apply, Matrix.submatrix_apply]
  by_cases hi : pK k r i <;> by_cases hj : pK k r j <;>
    simp [hi, hj, Equiv.sumCompl_symm_apply_of_pos, Equiv.sumCompl_symm_apply_of_neg]

/- English proof (translation)
Simplify using `only [Qm, Matrix.reindex_apply]`. Rewrite using `[Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`. Simplify using the standard rewrite rules.
-/
theorem Qm_mul (a c : Matrix {i // pK k r i} {i // pK k r i} ℂ) (b d : Matrix {i // ¬ pK k r i} {i // ¬ pK k r i} ℂ) :
    Qm a b * Qm c d = Qm (a * c) (b * d) := by
  simp only [Qm, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

/- English proof (translation)
Simplify using `[Qm, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]`.
-/
theorem Qm_conjTranspose (a : Matrix {i // pK k r i} {i // pK k r i} ℂ) (b : Matrix {i // ¬ pK k r i} {i // ¬ pK k r i} ℂ) :
    (Qm a b)ᴴ = Qm aᴴ bᴴ := by
  simp [Qm, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]

/- English proof (translation)
Simplify using `only [Qm, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map]`. Simplify using the standard rewrite rules.
-/
theorem Qm_map (a : Matrix {i // pK k r i} {i // pK k r i} ℂ) (b : Matrix {i // ¬ pK k r i} {i // ¬ pK k r i} ℂ) :
    (Qm a b).map (starRingEnd ℂ) = Qm (a.map (starRingEnd ℂ)) (b.map (starRingEnd ℂ)) := by
  simp only [Qm, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp

/- English proof (translation)
Simplify using `[Qm, Matrix.reindex_apply, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]`.
-/
theorem Qm_one : Qm (1 : Matrix {i // pK k r i} {i // pK k r i} ℂ) 1 = (1 : Mat k r) := by
  simp [Qm, Matrix.reindex_apply, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

/- English proof (translation)
Establish `h'` using `(Matrix.reindex (Equiv.sumCompl (pK k r)) (Equiv.sumCompl (pK k r))).injective h`. Conclude with `(Matrix.fromBlocks_inj.mp h').1`.
-/
theorem Qm_left_inj {a c : Matrix {i // pK k r i} {i // pK k r i} ℂ} {b d : Matrix {i // ¬ pK k r i} {i // ¬ pK k r i} ℂ}
    (h : Qm a b = Qm c d) : a = c := by
  have h' := (Matrix.reindex (Equiv.sumCompl (pK k r)) (Equiv.sumCompl (pK k r))).injective h
  exact (Matrix.fromBlocks_inj.mp h').1

/- English proof (translation)
Take `⟨h1, h2⟩` from `hi`. Unfold `Hpk`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[if_neg (by omega), if_neg (by omega), if_pos ⟨h1, by omega, rfl⟩, if_neg (by omega), if_pos rfl]`.

Rewrite using `[if_neg (by omega), if_neg (fun h => by have : i.val ≠ j.val := fun e => hij (Fin.ext e); omega), if_neg (fun h => hij h.2.2), if_neg hij]`.
-/
theorem Hpk_left (i j : Fin (2 * r + k + 1)) (hi : pK k r i) : Hpk k r i j = if i = j then 1 else 0 := by
  obtain ⟨h1, h2⟩ := hi
  unfold Hpk
  by_cases hij : i = j
  · subst hij
    rw [if_neg (by omega), if_neg (by omega), if_pos ⟨h1, by omega, rfl⟩, if_neg (by omega), if_pos rfl]
  · rw [if_neg (by omega), if_neg (fun h => by have : i.val ≠ j.val := fun e => hij (Fin.ext e); omega),
      if_neg (fun h => hij h.2.2), if_neg hij]

/- English proof (translation)
Take `⟨h1, h2⟩` from `hj`. Unfold `Hpk`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[if_neg (by omega), if_neg (by omega), if_pos ⟨h1, by omega, rfl⟩, if_neg (by omega), if_pos rfl]`.

Rewrite using `[if_neg (fun h => by have : i.val ≠ j.val := fun e => hij (Fin.ext e); omega), if_neg (by omega), if_neg (fun h => hij h.2.2), if_neg hij]`.
-/
theorem Hpk_right (i j : Fin (2 * r + k + 1)) (hj : pK k r j) : Hpk k r i j = if i = j then 1 else 0 := by
  obtain ⟨h1, h2⟩ := hj
  unfold Hpk
  by_cases hij : i = j
  · subst hij
    rw [if_neg (by omega), if_neg (by omega), if_pos ⟨h1, by omega, rfl⟩, if_neg (by omega), if_pos rfl]
  · rw [if_neg (fun h => by have : i.val ≠ j.val := fun e => hij (Fin.ext e); omega), if_neg (by omega),
      if_neg (fun h => hij h.2.2), if_neg hij]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Qm_apply]`. Distinguish the cases in `hi : pK k r i`. Rewrite using `[Hpk_left i j hi, dif_pos hi]`. Distinguish the cases in `hj : pK k r j`.

Rewrite using `[dif_pos hj, Matrix.one_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.

Rewrite using `[dif_neg hj, if_neg]`. Introduce and unpack `rfl`. Conclude with `hj hi`. Rewrite using `[dif_neg hi]`. Distinguish the cases in `hj : pK k r j`.

Rewrite using `[dif_pos hj, Hpk_right i j hj, if_neg]`. Introduce and unpack `rfl`. Conclude with `hi hj`. Rewrite using `[dif_neg hj]`. Both sides reduce to the same expression.
-/
theorem Hpk_eq_Qm : Hpk k r = Qm 1 ((Hpk k r).submatrix Subtype.val Subtype.val) := by
  ext i j
  rw [Qm_apply]
  by_cases hi : pK k r i
  · rw [Hpk_left i j hi, dif_pos hi]
    by_cases hj : pK k r j
    · rw [dif_pos hj, Matrix.one_apply]
      by_cases h : i = j
      · subst h; simp
      · simp [h]
    · rw [dif_neg hj, if_neg]
      rintro rfl
      exact hj hi
  · rw [dif_neg hi]
    by_cases hj : pK k r j
    · rw [dif_pos hj, Hpk_right i j hj, if_neg]
      rintro rfl
      exact hi hj
    · rw [dif_neg hj]
      rfl

/- English proof (translation)
Rewrite using `[← InvGrp.col_apply x i j, h]`. Simplify using `[bvec, Pi.single_apply]`.
-/
theorem col_fix (x : Mat k r) (j : Fin (2 * r + k + 1)) (h : x *ᵥ bvec j = bvec j) (i : Fin (2 * r + k + 1)) :
    x i j = if i = j then 1 else 0 := by
  rw [← InvGrp.col_apply x i j, h]
  simp [bvec, Pi.single_apply]

/- English proof (translation)
Establish `hc` using `col_fix x j hcol`. Establish `hrow : ∀ n, (xᴴ * Hpk k r) j n = Hpk k r j n`. Introduce `n`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single j]`. Simplify using `[Matrix.conjTranspose_apply, hc]`.

Introduce `m _ hm`. Simplify using `[Matrix.conjTranspose_apply, hc, hm]`. Simplify using the standard rewrite rules. Establish `key : (xᴴ * Hpk k r * x) j l = s * x i l`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`.

Rewrite using `[hrow, hH, if_pos rfl]`. Introduce `n _ hn`. Rewrite using `[hrow, hH, if_neg hn, zero_mul]`. Simplify using the standard rewrite rules. Establish `hx2 : xᴴ * Hpk k r * x = Hpk k r` using `hx`.

Rewrite `key` using `[hx2, hH]`. Distinguish the cases in `hil : i = l`. Substitute `hil` using the available equality. Rewrite `key` using `[if_pos rfl]`. Rewrite using `[if_pos rfl]`.

Conclude with `mul_left_cancel₀ hs (key.symm.trans (mul_one s).symm)`. Rewrite `key` using `[if_neg (Ne.symm hil)]`. Rewrite using `[if_neg hil]`. Conclude with `(mul_eq_zero.mp key.symm).resolve_left hs`.
-/
theorem row_fix (x : Mat k r) (hx : x ∈ UH (Hpk k r)) (i j : Fin (2 * r + k + 1)) (s : ℂ) (hs : s ≠ 0)
    (hcol : x *ᵥ bvec j = bvec j) (hH : ∀ l, Hpk k r j l = if l = i then s else 0) (l : Fin (2 * r + k + 1)) :
    x i l = if i = l then 1 else 0 := by
  have hc := col_fix x j hcol
  have hrow : ∀ n, (xᴴ * Hpk k r) j n = Hpk k r j n := by
    intro n
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · simp [Matrix.conjTranspose_apply, hc]
    · intro m _ hm
      simp [Matrix.conjTranspose_apply, hc, hm]
    · simp
  have key : (xᴴ * Hpk k r * x) j l = s * x i l := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hrow, hH, if_pos rfl]
    · intro n _ hn
      rw [hrow, hH, if_neg hn, zero_mul]
    · simp
  have hx2 : xᴴ * Hpk k r * x = Hpk k r := hx
  rw [hx2, hH] at key
  by_cases hil : i = l
  · subst hil
    rw [if_pos rfl] at key
    rw [if_pos rfl]
    exact mul_left_cancel₀ hs (key.symm.trans (mul_one s).symm)
  · rw [if_neg (Ne.symm hil)] at key
    rw [if_neg hil]
    exact (mul_eq_zero.mp key.symm).resolve_left hs

/- English proof (translation)
Establish `he : (esI k r a).val = 2 * r + k - a.val` using `rfl`. Establish `he2 : (eI k r a).val = a.val` using `rfl`. Establish `ha` using `a.isLt`. Unfold `Hpk`. Distinguish the cases in `hl : l = eI k r a`.

Establish `hv : l.val = a.val` using `by rw [hl, he2]`. Rewrite using `[if_neg (by omega), if_pos (by omega), if_pos hl]`. Establish `hv : l.val ≠ a.val` using `fun h => hl (Fin.ext (h.trans he2.symm))`. Rewrite using `[if_neg (by omega), if_neg (by omega), if_neg (fun h => by obtain ⟨_, h2, _⟩ := h; omega), if_neg hl]`.
-/
theorem Hpk_esI (a : Fin r) (l : Fin (2 * r + k + 1)) : Hpk k r (esI k r a) l = if l = eI k r a then 1 else 0 := by
  have he : (esI k r a).val = 2 * r + k - a.val := rfl
  have he2 : (eI k r a).val = a.val := rfl
  have ha := a.isLt
  unfold Hpk
  by_cases hl : l = eI k r a
  · have hv : l.val = a.val := by rw [hl, he2]
    rw [if_neg (by omega), if_pos (by omega), if_pos hl]
  · have hv : l.val ≠ a.val := fun h => hl (Fin.ext (h.trans he2.symm))
    rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => by obtain ⟨_, h2, _⟩ := h; omega), if_neg hl]

/- English proof (translation)
Establish `he : (esI k r a).val = 2 * r + k - a.val` using `rfl`. Establish `he2 : (eI k r a).val = a.val` using `rfl`. Establish `ha` using `a.isLt`. Establish `hlt` using `l.isLt`. Unfold `Hpk`.

Distinguish the cases in `hl : l = esI k r a`. Establish `hv : l.val = 2 * r + k - a.val` using `by rw [hl, he]`. Rewrite using `[if_pos (by omega), if_pos hl]`. Establish `hv : l.val ≠ 2 * r + k - a.val` using `fun h => hl (Fin.ext (h.trans he.symm))`. Rewrite using `[if_neg (by omega), if_neg (by omega), if_neg (fun h => by obtain ⟨h1, _, _⟩ := h; omega), if_neg hl]`.
-/
theorem Hpk_eI (a : Fin r) (l : Fin (2 * r + k + 1)) : Hpk k r (eI k r a) l = if l = esI k r a then 1 else 0 := by
  have he : (esI k r a).val = 2 * r + k - a.val := rfl
  have he2 : (eI k r a).val = a.val := rfl
  have ha := a.isLt
  have hlt := l.isLt
  unfold Hpk
  by_cases hl : l = esI k r a
  · have hv : l.val = 2 * r + k - a.val := by rw [hl, he]
    rw [if_pos (by omega), if_pos hl]
  · have hv : l.val ≠ 2 * r + k - a.val := fun h => hl (Fin.ext (h.trans he.symm))
    rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => by obtain ⟨h1, _, _⟩ := h; omega), if_neg hl]

/- English proof (translation)
Establish `hw : (wI k r (Fin.last k)).val = r + k` using `rfl`. Unfold `Hpk`. Distinguish the cases in `hl : l = wI k r (Fin.last k)`. Substitute `hl` using the available equality. Rewrite using `[if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩, if_pos hw, if_pos rfl]`.

Rewrite using `[if_neg (by omega), if_neg (by omega), if_neg (fun h => hl h.2.2.symm), if_neg hl]`.
-/
theorem Hpk_wlast (l : Fin (2 * r + k + 1)) :
    Hpk k r (wI k r (Fin.last k)) l = if l = wI k r (Fin.last k) then -1 else 0 := by
  have hw : (wI k r (Fin.last k)).val = r + k := rfl
  unfold Hpk
  by_cases hl : l = wI k r (Fin.last k)
  · subst hl
    rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩, if_pos hw, if_pos rfl]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => hl h.2.2.symm), if_neg hl]

/- English proof (translation)
Unfold `pK at hj`. Establish `hjlt` using `j.isLt`. Distinguish the cases in `h1 : j.val < r`. Conclude with `Or.inl ⟨⟨j.val, h1⟩, Fin.ext rfl⟩`. Distinguish the cases in `h2 : j.val = r + k`.

Conclude with `Or.inr (Or.inr (Fin.ext h2))`. Use `Or.inr (Or.inl ⟨⟨2 * r + k - j.val, by omega⟩, Fin.ext ?_⟩) show j.val = 2 * r + k - (2 * r + k - j.val)` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers.
-/
theorem not_pK_cases (j : Fin (2 * r + k + 1)) (hj : ¬ pK k r j) :
    (∃ a : Fin r, j = eI k r a) ∨ (∃ a : Fin r, j = esI k r a) ∨ j = wI k r (Fin.last k) := by
  unfold pK at hj
  have hjlt := j.isLt
  by_cases h1 : j.val < r
  · exact Or.inl ⟨⟨j.val, h1⟩, Fin.ext rfl⟩
  · by_cases h2 : j.val = r + k
    · exact Or.inr (Or.inr (Fin.ext h2))
    · refine Or.inr (Or.inl ⟨⟨2 * r + k - j.val, by omega⟩, Fin.ext ?_⟩)
      show j.val = 2 * r + k - (2 * r + k - j.val)
      omega

/- English proof (translation)
Break down `not_pK_cases j hj with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl` into its components or cases. Conclude with `(he a).1`. Conclude with `(he a).2`. Conclude with `hl`.
-/
private theorem mulVec_bvec_eq_of_fix_e_es_last_not_pK (x : Mat k r)
    (he : ∀ a : Fin r, x *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ x *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (hl : x *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k)))
    (j : Fin (2 * r + k + 1)) (hj : ¬ pK k r j) : x *ᵥ bvec j = bvec j := by
  rcases not_pK_cases j hj with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl
  · exact (he a).1
  · exact (he a).2
  · exact hl

/- English proof (translation)
Break down `not_pK_cases i hi with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl` into its components or cases. Conclude with `row_fix x hx (eI k r a) (esI k r a) 1 one_ne_zero (he a).2 (Hpk_esI a) l`. Conclude with `row_fix x hx (esI k r a) (eI k r a) 1 one_ne_zero (he a).1 (Hpk_eI a) l`. Conclude with `row_fix x hx _ _ (-1) (neg_ne_zero.mpr one_ne_zero) hl (fun l => Hpk_wlast l) l`.
-/
private theorem apply_eq_ite_of_fix_e_es_last_not_pK (x : Mat k r) (hx : x ∈ UH (Hpk k r))
    (he : ∀ a : Fin r, x *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ x *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (hl : x *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k)))
    (i : Fin (2 * r + k + 1)) (hi : ¬ pK k r i) (l : Fin (2 * r + k + 1)) :
    x i l = if i = l then 1 else 0 := by
  rcases not_pK_cases i hi with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl
  · exact row_fix x hx (eI k r a) (esI k r a) 1 one_ne_zero (he a).2 (Hpk_esI a) l
  · exact row_fix x hx (esI k r a) (eI k r a) 1 one_ne_zero (he a).1 (Hpk_eI a) l
  · exact row_fix x hx _ _ (-1) (neg_ne_zero.mpr one_ne_zero) hl (fun l => Hpk_wlast l) l

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Qm_apply]`. Distinguish the cases in `hi : pK k r i`. Rewrite using `[dif_pos hi]`. Distinguish the cases in `hj : pK k r j`.

Rewrite using `[dif_pos hj]`. Both sides reduce to the same expression. Rewrite using `[dif_neg hj, col_fix x j (mulVec_bvec_eq_of_fix_e_es_last_not_pK x he hl j hj) i, if_neg]`. Introduce and unpack `rfl`. Conclude with `hj hi`.

Rewrite using `[dif_neg hi, apply_eq_ite_of_fix_e_es_last_not_pK x hx he hl i hi j]`. Distinguish the cases in `hj : pK k r j`. Rewrite using `[dif_pos hj, if_neg]`. Introduce and unpack `rfl`. Conclude with `hi hj`.

Rewrite using `[dif_neg hj, Matrix.one_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem eq_Qm (x : Mat k r) (hx : x ∈ UH (Hpk k r))
    (he : ∀ a : Fin r, x *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ x *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (hl : x *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k))) :
    x = Qm (x.submatrix Subtype.val Subtype.val) 1 := by
  ext i j
  rw [Qm_apply]
  by_cases hi : pK k r i
  · rw [dif_pos hi]
    by_cases hj : pK k r j
    · rw [dif_pos hj]
      rfl
    · rw [dif_neg hj, col_fix x j (mulVec_bvec_eq_of_fix_e_es_last_not_pK x he hl j hj) i, if_neg]
      rintro rfl
      exact hj hi
  · rw [dif_neg hi, apply_eq_ite_of_fix_e_es_last_not_pK x hx he hl i hi j]
    by_cases hj : pK k r j
    · rw [dif_pos hj, if_neg]
      rintro rfl
      exact hi hj
    · rw [dif_neg hj, Matrix.one_apply]
      by_cases h : i = j
      · subst h; simp
      · simp [h]

/- English proof (translation)
Establish `h : (Qm m 1)ᴴ * Hpk k r * Qm m 1 = Hpk k r` using `hx`. Rewrite `h` using `[Hpk_eq_Qm, Qm_conjTranspose, Qm_mul, Qm_mul]`. Simplify using `only [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul] at h`. Conclude with `Qm_left_inj h`.
-/
theorem unitary_of_Qm (m : Matrix {i // pK k r i} {i // pK k r i} ℂ) (hx : Qm m 1 ∈ UH (Hpk k r)) : mᴴ * m = 1 := by
  have h : (Qm m 1)ᴴ * Hpk k r * Qm m 1 = Hpk k r := hx
  rw [Hpk_eq_Qm, Qm_conjTranspose, Qm_mul, Qm_mul] at h
  simp only [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul] at h
  exact Qm_left_inj h

/- English proof (translation)
Use `show (Qm U 1)ᴴ * Hpk k r * Qm U 1 = Hpk k r`. Rewrite using `[Hpk_eq_Qm, Qm_conjTranspose, Qm_mul, Qm_mul]`. Simplify using `only [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul, hU]`.
-/
theorem Qm_mem_UH (U : Matrix {i // pK k r i} {i // pK k r i} ℂ) (hU : Uᴴ * U = 1) : Qm U 1 ∈ UH (Hpk k r) := by
  show (Qm U 1)ᴴ * Hpk k r * Qm U 1 = Hpk k r
  rw [Hpk_eq_Qm, Qm_conjTranspose, Qm_mul, Qm_mul]
  simp only [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul, hU]

/- English proof (translation)
Use extensionality with `i`. Rewrite using `[InvGrp.col_apply, Qm_apply]`. Simplify using `only [bvec, Pi.single_apply]`. Distinguish the cases in `hi : pK k r i`. Rewrite using `[dif_pos hi, dif_neg hj, if_neg]`.

Introduce and unpack `rfl`. Conclude with `hj hi`. Rewrite using `[dif_neg hi, dif_neg hj, Matrix.one_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem Qm_fix_off (U : Matrix {i // pK k r i} {i // pK k r i} ℂ) (j : Fin (2 * r + k + 1)) (hj : ¬ pK k r j) :
    Qm U 1 *ᵥ bvec j = bvec j := by
  ext i
  rw [InvGrp.col_apply, Qm_apply]
  simp only [bvec, Pi.single_apply]
  by_cases hi : pK k r i
  · rw [dif_pos hi, dif_neg hj, if_neg]
    rintro rfl
    exact hj hi
  · rw [dif_neg hi, dif_neg hj, Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h]

/- English proof (translation)
Distinguish the cases in `hj : pK k r j`. Use extensionality with `i`. Rewrite using `[InvGrp.col_apply, Qm_apply]`. Establish `h2 : (fun s : {i // pK k r i} => bvec j s.1) = Pi.single ⟨j, hj⟩ 1`. Use extensionality with `s`.

Simplify using `only [bvec, Pi.single_apply, Subtype.ext_iff]`. Rewrite `hU` using `[h2]`. Distinguish the cases in `hi : pK k r i`. Rewrite using `[dif_pos hi, dif_pos hj]`. Use `congrFun hU ⟨i, hi⟩` as an intermediate fact.

Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply] at this`. Simplify using `[bvec, Pi.single_apply, this]`. Rewrite using `[dif_neg hi, dif_pos hj]`. Simplify using `only [bvec, Pi.single_apply]`. Rewrite using `[if_neg]`.

Introduce and unpack `rfl`. Conclude with `hi hj`. Conclude with `Qm_fix_off U j hj`.
-/
theorem Qm_fix_vec (U : Matrix {i // pK k r i} {i // pK k r i} ℂ) (j : Fin (2 * r + k + 1))
    (hU : U *ᵥ (fun s => bvec j s.1) = fun s => bvec j s.1) : Qm U 1 *ᵥ bvec j = bvec j := by
  by_cases hj : pK k r j
  · ext i
    rw [InvGrp.col_apply, Qm_apply]
    have h2 : (fun s : {i // pK k r i} => bvec j s.1) = Pi.single ⟨j, hj⟩ 1 := by
      ext s
      simp only [bvec, Pi.single_apply, Subtype.ext_iff]
    rw [h2] at hU
    by_cases hi : pK k r i
    · rw [dif_pos hi, dif_pos hj]
      have := congrFun hU ⟨i, hi⟩
      simp [Matrix.mulVec, dotProduct, Pi.single_apply] at this
      simp [bvec, Pi.single_apply, this]
    · rw [dif_neg hi, dif_pos hj]
      simp only [bvec, Pi.single_apply]
      rw [if_neg]
      rintro rfl
      exact hi hj
  · exact Qm_fix_off U j hj

end TransM

end ReciprocityTheory.ChartRestriction.DS.Mult1
