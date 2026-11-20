import Formalism.SatakeDualWeyl.Statement

namespace Formalism.UG.P

open Matrix

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `(ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply])`.
-/
theorem sigex_cT_conj_eq {m p : Type} (M : Matrix m p ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  first
    | rfl
    | (ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply])

noncomputable def scal {n : Type} (ev : n → ℝ) : n → ℂ := fun i => (((Real.sqrt |ev i|)⁻¹ : ℝ) : ℂ)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Pi.star_apply, scal]`. Conclude with `Complex.conj_ofReal _`.
-/
theorem star_scal {n : Type} (ev : n → ℝ) : star (scal ev) = scal ev := by
  funext i
  simp only [Pi.star_apply, scal]
  exact Complex.conj_ofReal _

/- English proof (translation)
Establish `key : (Real.sqrt |ev i|)⁻¹ * ev i * (Real.sqrt |ev i|)⁻¹ = ev i / |ev i|` using `by set t := Real.sqrt |ev i| with ht`. Establish `hs : t * t = |ev i|` using `Real.mul_self_sqrt (abs_nonneg _)`. Rewrite using `[div_eq_mul_inv, ← hs]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [scal]`.

Rewrite using `[← key]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem scal_sq {n : Type} (ev : n → ℝ) (i : n) :
    scal ev i * (ev i : ℂ) * scal ev i = ((ev i / |ev i| : ℝ) : ℂ) := by
  have key : (Real.sqrt |ev i|)⁻¹ * ev i * (Real.sqrt |ev i|)⁻¹ = ev i / |ev i| := by
    set t := Real.sqrt |ev i| with ht
    have hs : t * t = |ev i| := Real.mul_self_sqrt (abs_nonneg _)
    rw [div_eq_mul_inv, ← hs]
    ring
  simp only [scal]
  rw [← key]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, star_scal]`. Establish `hU : ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * (hJ.eigenvectorUnitary : Matrix n n ℂ) = 1`. Establish `h` using `Unitary.star_mul_self_of_mem hJ.eigenvectorUnitary.2`. Rewrite `h` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Establish `key : ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * J * (hJ.eigenvectorUnitary : Matrix n n ℂ) = diagonal (RCLike.ofReal ∘ hJ.eigenvalues)`.

Establish `h1` using `congrArg (fun M => ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * M * (hJ.eigenvectorUnitary : Matrix n n ℂ)) hJ.spectral_theorem`. Use `first`. Consider the case `simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h1`. Consider the case `simp only [Unitary.conjStarAlgAut, Matrix.star_eq_conjTranspose] at h1`. Rewrite using `[h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by`. Rewrite using `[key, diagonal_mul_diagonal, diagonal_mul_diagonal]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Conclude with `scal_sq _ i`.
-/
theorem herm_diag {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ}
    (hJ : J.IsHermitian) :
    ((hJ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hJ.eigenvalues))ᴴ * J *
        ((hJ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hJ.eigenvalues)) =
      diagonal (fun i => ((hJ.eigenvalues i / |hJ.eigenvalues i| : ℝ) : ℂ)) := by
  rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, star_scal]
  have hU : ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * (hJ.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
    have h := Unitary.star_mul_self_of_mem hJ.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h
  have key : ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * J * (hJ.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (RCLike.ofReal ∘ hJ.eigenvalues) := by
    have h1 := congrArg (fun M => ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * M *
      (hJ.eigenvectorUnitary : Matrix n n ℂ)) hJ.spectral_theorem
    first
      | simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h1
      | simp only [Unitary.conjStarAlgAut, Matrix.star_eq_conjTranspose] at h1
    rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one]
  calc _ = diagonal (scal hJ.eigenvalues) * (((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * J *
          (hJ.eigenvectorUnitary : Matrix n n ℂ)) * diagonal (scal hJ.eigenvalues) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [key, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext i
        exact scal_sq _ i

/- English proof (translation)
Introduce `h0`. Apply `hdet.ne_zero` to reduce the goal to its premises. Rewrite using `[hJ.det_eq_prod_eigenvalues]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])`.
-/
theorem eig_ne_zero {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ}
    (hJ : J.IsHermitian) (hdet : IsUnit J.det) (i : n) : hJ.eigenvalues i ≠ 0 := by
  intro h0
  apply hdet.ne_zero
  rw [hJ.det_eq_prod_eigenvalues]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])

/- English proof (translation)
Rewrite using `[abs_of_pos h, div_self h.ne']`.
-/
theorem sign_pos {x : ℝ} (h : 0 < x) : x / |x| = 1 := by
  rw [abs_of_pos h, div_self h.ne']

/- English proof (translation)
Rewrite using `[abs_of_neg h, div_neg, div_self h.ne]`.
-/
theorem sign_neg {x : ℝ} (h : x < 0) : x / |x| = -1 := by
  rw [abs_of_neg h, div_neg, div_self h.ne]

/- English proof (translation)
Unfold `Formalism.UG.SigExists`. Introduce `n _ _ J hJ hdet`. Unfold `Formalism.UG.IsHerm at hJ`. Unfold `Formalism.UG.HasSignature`. Unfold `Formalism.UG.Jpq`.

Establish `hH : J.IsHermitian` using `(sigex_cT_conj_eq J).symm.trans hJ`. Establish `hU : ((hH.eigenvectorUnitary : Matrix n n ℂ))ᴴ * (hH.eigenvectorUnitary : Matrix n n ℂ) = 1`. Establish `h` using `Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2`. Rewrite `h` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Take `⟨Q, hQdef⟩ : ∃ Q : Matrix n n ℂ, Q = (hH.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hH.eigenvalues)` from `⟨_, rfl⟩`.

Establish `hQ : Qᴴ * J * Q = diagonal (fun i => ((hH.eigenvalues i / |hH.eigenvalues i| : ℝ) : ℂ))`. Rewrite using `[hQdef]`. Conclude with `herm_diag hH`. Take `⟨e, he⟩ : ∃ e : n ≃ Fin (Fintype.card {i // 0 < hH.eigenvalues i}) ⊕ Fin (Fintype.card {i // ¬ 0 < hH.eigenvalues i}), e = (Equiv.sumCompl (fun i => 0 < hH.eigenvalues i)).symm.trans (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))` from `⟨_, rfl⟩`. Establish `hinl : ∀ a, e.symm (Sum.inl a) = ((Fintype.equivFin {i // 0 < hH.eigenvalues i}).symm a : n)`.

Introduce `a`. Rewrite using `[he]`. Apply the tactic sequence `first | rfl | simp`. Establish `hinr : ∀ a, e.symm (Sum.inr a) = ((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a : n)`. Introduce `a`.

Rewrite using `[he]`. Apply the tactic sequence `first | rfl | simp`. Establish `hdetQ : IsUnit (reindex e e Q).det`. Rewrite using `[Matrix.det_reindex_self, hQdef, Matrix.det_mul, Matrix.det_diagonal]`. Use `IsUnit.mul (Matrix.isUnit_det_of_left_inverse hU) ?_` and prove the remaining obligations.

Rewrite using `[isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]`. Introduce `i _`. Establish `h1 : hH.eigenvalues i ≠ 0` using `eig_ne_zero hH hdet i`. Simplify using `only [scal, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]`. Conclude with `(Real.sqrt_pos.mpr (abs_pos.mpr h1)).ne'`.

Use `⟨_, _, e, Matrix.nonsingInvUnit _ hdetQ, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Formalism.UG.cT (starRingEnd ℂ) (reindex e e Q) * reindex e e J * reindex e e Q = _`. Rewrite using `[sigex_cT_conj_eq]`. Simplify using `only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]`. Rewrite using `[hQ, Matrix.submatrix_diagonal_equiv]`.

Use extensionality with `(a | a) (b | b)`. Simplify using `only [Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply, Function.comp_apply, hinl, Sum.inl.injEq, Matrix.one_apply] split_ifs`. Rewrite using `[sign_pos ((Fintype.equivFin {i // 0 < hH.eigenvalues i}).symm a).2, Complex.ofReal_one]`. Both sides reduce to the same expression. Simplify using `[Matrix.diagonal_apply]`.

Simplify using `[Matrix.diagonal_apply]`. Simplify using `only [Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply, Function.comp_apply, hinr, Sum.inr.injEq, Matrix.neg_apply, Matrix.one_apply] split_ifs`. Establish `hx` using `((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a).2`. Establish `hneg : hH.eigenvalues ((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a : n) < 0` using `lt_of_le_of_ne (not_lt.mp hx) (eig_ne_zero hH hdet _)`. Rewrite using `[sign_neg hneg]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem signature_exists : Formalism.UG.SigExists := by
  unfold Formalism.UG.SigExists
  intro n _ _ J hJ hdet
  unfold Formalism.UG.IsHerm at hJ
  unfold Formalism.UG.HasSignature
  unfold Formalism.UG.Jpq
  have hH : J.IsHermitian := (sigex_cT_conj_eq J).symm.trans hJ
  have hU : ((hH.eigenvectorUnitary : Matrix n n ℂ))ᴴ * (hH.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
    have h := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix n n ℂ,
      Q = (hH.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hH.eigenvalues) := ⟨_, rfl⟩
  have hQ : Qᴴ * J * Q = diagonal (fun i => ((hH.eigenvalues i / |hH.eigenvalues i| : ℝ) : ℂ)) := by
    rw [hQdef]
    exact herm_diag hH
  obtain ⟨e, he⟩ : ∃ e : n ≃ Fin (Fintype.card {i // 0 < hH.eigenvalues i}) ⊕
      Fin (Fintype.card {i // ¬ 0 < hH.eigenvalues i}),
      e = (Equiv.sumCompl (fun i => 0 < hH.eigenvalues i)).symm.trans
        (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _)) := ⟨_, rfl⟩
  have hinl : ∀ a, e.symm (Sum.inl a) =
      ((Fintype.equivFin {i // 0 < hH.eigenvalues i}).symm a : n) := by
    intro a
    rw [he]
    first | rfl | simp
  have hinr : ∀ a, e.symm (Sum.inr a) =
      ((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a : n) := by
    intro a
    rw [he]
    first | rfl | simp
  have hdetQ : IsUnit (reindex e e Q).det := by
    rw [Matrix.det_reindex_self, hQdef, Matrix.det_mul, Matrix.det_diagonal]
    refine IsUnit.mul (Matrix.isUnit_det_of_left_inverse hU) ?_
    rw [isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i _
    have h1 : hH.eigenvalues i ≠ 0 := eig_ne_zero hH hdet i
    simp only [scal, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (Real.sqrt_pos.mpr (abs_pos.mpr h1)).ne'
  refine ⟨_, _, e, Matrix.nonsingInvUnit _ hdetQ, ?_⟩
  change Formalism.UG.cT (starRingEnd ℂ) (reindex e e Q) * reindex e e J * reindex e e Q = _
  rw [sigex_cT_conj_eq]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rw [hQ, Matrix.submatrix_diagonal_equiv]
  ext (a | a) (b | b)
  · simp only [Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply, Function.comp_apply, hinl,
      Sum.inl.injEq, Matrix.one_apply]
    split_ifs
    · rw [sign_pos ((Fintype.equivFin {i // 0 < hH.eigenvalues i}).symm a).2, Complex.ofReal_one]
    · rfl
  · simp [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply]
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply, Function.comp_apply, hinr,
      Sum.inr.injEq, Matrix.neg_apply, Matrix.one_apply]
    split_ifs
    · have hx := ((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a).2
      have hneg : hH.eigenvalues ((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a : n) < 0 :=
        lt_of_le_of_ne (not_lt.mp hx) (eig_ne_zero hH hdet _)
      rw [sign_neg hneg]
      push_cast
      ring
    · simp

end Formalism.UG.P
