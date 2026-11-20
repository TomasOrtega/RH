import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

variable {n : ℕ}

/- English proof (translation)
Establish `h : JJ n * JJ n = fromBlocks (-1) (-0) (-0) (-1)`. Simplify using `[JJ, fromBlocks_multiply]`. Rewrite using `[h, ← fromBlocks_neg, fromBlocks_one]`.
-/
lemma jj_mul_jj : JJ n * JJ n = -1 := by
  have h : JJ n * JJ n = fromBlocks (-1) (-0) (-0) (-1) := by
    simp [JJ, fromBlocks_multiply]
  rw [h, ← fromBlocks_neg, fromBlocks_one]

/- English proof (translation)
Establish `h1 : (Y * JJ n * Yᴴ * JJ n) * Y = (-1) * Y`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : Y * JJ n * Yᴴ * JJ n = -1` using `hU.mul_left_inj.mp h1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, Matrix.mul_neg, jj_mul_jj, neg_neg, Matrix.mul_one]`.

Use `_ = JJ n := by rw [h2]; simp`.
-/
lemma conj_jj {Y : M2 n} (hU : IsUnit Y) (hG : Yᴴ * JJ n * Y = JJ n) : Y * JJ n * Yᴴ = JJ n := by
  have h1 : (Y * JJ n * Yᴴ * JJ n) * Y = (-1) * Y := by
    calc (Y * JJ n * Yᴴ * JJ n) * Y = Y * JJ n * (Yᴴ * JJ n * Y) := by simp only [Matrix.mul_assoc]
      _ = Y * (JJ n * JJ n) := by rw [hG, Matrix.mul_assoc]
      _ = (-1) * Y := by rw [jj_mul_jj]; simp
  have h2 : Y * JJ n * Yᴴ * JJ n = -1 := hU.mul_left_inj.mp h1
  calc Y * JJ n * Yᴴ = (Y * JJ n * Yᴴ * JJ n) * (-JJ n) := by
        simp only [Matrix.mul_assoc, Matrix.mul_neg, jj_mul_jj, neg_neg, Matrix.mul_one]
    _ = JJ n := by rw [h2]; simp

/- English proof (translation)
Simplify using `only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul] at h`. Take `⟨-, h12, -, h22⟩` from `fromBlocks_inj.mp h`. Conclude with `⟨(neg_add_eq_zero.mp h22).symm, by rw [sub_eq_neg_add]; exact h12⟩`.
-/
lemma rows_rel {A B C Dm : Matrix (Fin n) (Fin n) ℂ}
    (h : fromBlocks A B C Dm * JJ n * (fromBlocks A B C Dm)ᴴ = JJ n) :
    C * Dmᴴ = Dm * Cᴴ ∧ A * Dmᴴ - B * Cᴴ = 1 := by
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.mul_zero, add_zero,
    zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul] at h
  obtain ⟨-, h12, -, h22⟩ := fromBlocks_inj.mp h
  exact ⟨(neg_add_eq_zero.mp h22).symm, by rw [sub_eq_neg_add]; exact h12⟩

/- English proof (translation)
Introduce `hd`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hd`. Establish `e : star v ⬝ᵥ ((C * Cᴴ + Dm * Dmᴴ) *ᵥ v) = star (Cᴴ *ᵥ v) ⬝ᵥ (Cᴴ *ᵥ v) + star (Dmᴴ *ᵥ v) ⬝ᵥ (Dmᴴ *ᵥ v)`. Rewrite using `[star_mulVec, star_mulVec, conjTranspose_conjTranspose, conjTranspose_conjTranspose, ← dotProduct_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← dotProduct_add, ← add_mulVec]`. Rewrite `e` using `[hv, dotProduct_zero]`.

Establish `n1` using `dotProduct_star_self_nonneg (Cᴴ *ᵥ v)`. Establish `n2` using `dotProduct_star_self_nonneg (Dmᴴ *ᵥ v)`. Take `⟨z1, z2⟩` from `(add_eq_zero_iff_of_nonneg n1 n2).mp e.symm`. Establish `hC : Cᴴ *ᵥ v = 0` using `dotProduct_star_self_eq_zero.mp z1`. Establish `hD : Dmᴴ *ᵥ v = 0` using `dotProduct_star_self_eq_zero.mp z2`.

Establish `: (A * Dmᴴ - B * Cᴴ) *ᵥ v = 0`. Rewrite using `[sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hC, hD, mulVec_zero, mulVec_zero, sub_zero]`. Rewrite `this` using `[h, one_mulVec]`. Conclude with `hv0 this`.
-/
lemma det_S_ne {A B C Dm : Matrix (Fin n) (Fin n) ℂ} (h : A * Dmᴴ - B * Cᴴ = 1) :
    (C * Cᴴ + Dm * Dmᴴ).det ≠ 0 := by
  intro hd
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have e : star v ⬝ᵥ ((C * Cᴴ + Dm * Dmᴴ) *ᵥ v) =
      star (Cᴴ *ᵥ v) ⬝ᵥ (Cᴴ *ᵥ v) + star (Dmᴴ *ᵥ v) ⬝ᵥ (Dmᴴ *ᵥ v) := by
    rw [star_mulVec, star_mulVec, conjTranspose_conjTranspose, conjTranspose_conjTranspose, ← dotProduct_mulVec,
      ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← dotProduct_add, ← add_mulVec]
  rw [hv, dotProduct_zero] at e
  have n1 := dotProduct_star_self_nonneg (Cᴴ *ᵥ v)
  have n2 := dotProduct_star_self_nonneg (Dmᴴ *ᵥ v)
  obtain ⟨z1, z2⟩ := (add_eq_zero_iff_of_nonneg n1 n2).mp e.symm
  have hC : Cᴴ *ᵥ v = 0 := dotProduct_star_self_eq_zero.mp z1
  have hD : Dmᴴ *ᵥ v = 0 := dotProduct_star_self_eq_zero.mp z2
  have : (A * Dmᴴ - B * Cᴴ) *ᵥ v = 0 := by
    rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hC, hD, mulVec_zero, mulVec_zero, sub_zero]
  rw [h, one_mulVec] at this
  exact hv0 this

/- English proof (translation)
Establish `hg : g = fromBlocks g.toBlocks₁₁ g.toBlocks₁₂ g.toBlocks₂₁ g.toBlocks₂₂` using `(fromBlocks_toBlocks g).symm`. Establish `hr` using `(rows_rel (A := g.toBlocks₁₁) (B := g.toBlocks₁₂) (by rw [← hg]; exact h2)).1`. Establish `hn : g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ = 1`. Establish `h` using `h1`. Rewrite `h` using `[hg, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]`.

Conclude with `(fromBlocks_inj.mp h).2.2.2`. Establish `hs : star Complex.I = -Complex.I` using `by simp`. Establish `hI' : -Complex.I * Complex.I = 1` using `by rw [neg_mul, Complex.I_mul_I, neg_neg]`. Establish `key : u1 g * (u1 g)ᴴ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ`. Rewrite using `[u1, conjTranspose_add, conjTranspose_smul, hs, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]`.

Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hI', one_smul, hr]`. Rewrite using `[neg_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[key, hn]`.
-/
lemma first_cayley_block_mul_conjTranspose {g : M2 n} (h1 : g * gᴴ = 1) (h2 : g * JJ n * gᴴ = JJ n) : u1 g * (u1 g)ᴴ = 1 := by
  have hg : g = fromBlocks g.toBlocks₁₁ g.toBlocks₁₂ g.toBlocks₂₁ g.toBlocks₂₂ := (fromBlocks_toBlocks g).symm
  have hr := (rows_rel (A := g.toBlocks₁₁) (B := g.toBlocks₁₂) (by rw [← hg]; exact h2)).1
  have hn : g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ = 1 := by
    have h := h1
    rw [hg, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one] at h
    exact (fromBlocks_inj.mp h).2.2.2
  have hs : star Complex.I = -Complex.I := by simp
  have hI' : -Complex.I * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  have key : u1 g * (u1 g)ᴴ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
    rw [u1, conjTranspose_add, conjTranspose_smul, hs, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hI', one_smul, hr]
    rw [neg_smul]
    abel
  rw [key, hn]

/- English proof (translation)
Establish `h` using `congrArg (fun M => ‖Matrix.det M‖) (first_cayley_block_mul_conjTranspose h1 h2)`. Simplify using `only [det_mul, det_conjTranspose, det_one, norm_mul, norm_star, norm_one] at h`. Use polynomial arithmetic with `[norm_nonneg (u1 g).det]`.
-/
lemma norm_det_first_cayley_block_unitary {g : M2 n} (h1 : g * gᴴ = 1) (h2 : g * JJ n * gᴴ = JJ n) : ‖(u1 g).det‖ = 1 := by
  have h := congrArg (fun M => ‖Matrix.det M‖) (first_cayley_block_mul_conjTranspose h1 h2)
  simp only [det_mul, det_conjTranspose, det_one, norm_mul, norm_star, norm_one] at h
  nlinarith [norm_nonneg (u1 g).det]

/- English proof (translation)
Establish `hm : mR (q * k₀) = mR q * mR k₀` using `rfl`. Establish `hQG : InG (mR q)` using `q.2`. Take `⟨A, B, Dd, hQ⟩ : ∃ A B Dd : Matrix (Fin n) (Fin n) ℂ, mR q = fromBlocks A B 0 Dd` from `⟨(mR q).toBlocks₁₁, (mR q).toBlocks₁₂, (mR q).toBlocks₂₂, by conv_lhs => rw [← fromBlocks_toBlocks (mR q)]`. Rewrite using `[hq]⟩`. Establish `hAD : Aᴴ * Dd = 1`.

Establish `h` using `hQG`. Unfold `InG at h`. Rewrite `h` using `[hQ]`. Simplify using `only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, conjTranspose_zero, neg_zero] at h`. Conclude with `(fromBlocks_inj.mp h).2.1`.

Establish `hK1 : mR k₀ * (mR k₀)ᴴ = 1` using `mul_eq_one_comm.mp hk.2`. Establish `hK2 : mR k₀ * JJ n * (mR k₀)ᴴ = JJ n` using `conj_jj k₀.1.isUnit hk.1`. Establish `hu : u1 (mR q * mR k₀) = Dd * u1 (mR k₀)`. Rewrite using `[hQ]`. Use `conv_lhs => rw [← fromBlocks_toBlocks (mR k₀)]`.

Simplify using `only [u1, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add, Matrix.mul_add, Matrix.mul_smul]`. Establish `hdet : ‖A.det‖ * ‖Dd.det‖ = 1`. Establish `h` using `congrArg (fun M => ‖Matrix.det M‖) hAD`. Simplify `h` using `only [det_mul, det_conjTranspose, norm_mul, norm_star, det_one, norm_one]`. Establish `hA0 : ‖A.det‖ ≠ 0`.

Introduce `h0`. Rewrite `hdet` using `[h0, zero_mul]`. Conclude with `zero_ne_one hdet`. Establish `hDd : ‖Dd.det‖ = 1 / ‖A.det‖` using `eq_one_div_of_mul_eq_one_right hdet`. Unfold `hLoc`.

Rewrite using `[hm, hu, det_mul, norm_mul, norm_det_first_cayley_block_unitary hK1 hK2, mul_one, hQ, toBlocks_fromBlocks₁₁, hDd, one_div, inv_pow, inv_inv]`.
-/
theorem hLoc_mul (q k₀ : GR n) (hq : (mR q).toBlocks₂₁ = 0) (hk : InK (mR k₀)) :
    hLoc (q * k₀) = ‖(mR q).toBlocks₁₁.det‖ ^ 2 := by
  have hm : mR (q * k₀) = mR q * mR k₀ := rfl
  have hQG : InG (mR q) := q.2
  obtain ⟨A, B, Dd, hQ⟩ : ∃ A B Dd : Matrix (Fin n) (Fin n) ℂ, mR q = fromBlocks A B 0 Dd :=
    ⟨(mR q).toBlocks₁₁, (mR q).toBlocks₁₂, (mR q).toBlocks₂₂, by
      conv_lhs => rw [← fromBlocks_toBlocks (mR q)]
      rw [hq]⟩
  have hAD : Aᴴ * Dd = 1 := by
    have h := hQG
    unfold InG at h
    rw [hQ] at h
    simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, conjTranspose_zero, neg_zero] at h
    exact (fromBlocks_inj.mp h).2.1
  have hK1 : mR k₀ * (mR k₀)ᴴ = 1 := mul_eq_one_comm.mp hk.2
  have hK2 : mR k₀ * JJ n * (mR k₀)ᴴ = JJ n := conj_jj k₀.1.isUnit hk.1
  have hu : u1 (mR q * mR k₀) = Dd * u1 (mR k₀) := by
    rw [hQ]
    conv_lhs => rw [← fromBlocks_toBlocks (mR k₀)]
    simp only [u1, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.mul_add, Matrix.mul_smul]
  have hdet : ‖A.det‖ * ‖Dd.det‖ = 1 := by
    have h := congrArg (fun M => ‖Matrix.det M‖) hAD
    simpa only [det_mul, det_conjTranspose, norm_mul, norm_star, det_one, norm_one] using h
  have hA0 : ‖A.det‖ ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hdet; exact zero_ne_one hdet
  have hDd : ‖Dd.det‖ = 1 / ‖A.det‖ := eq_one_div_of_mul_eq_one_right hdet
  unfold hLoc
  rw [hm, hu, det_mul, norm_mul, norm_det_first_cayley_block_unitary hK1 hK2, mul_one, hQ, toBlocks_fromBlocks₁₁, hDd, one_div, inv_pow,
    inv_inv]

/- English proof (translation)
Establish `hpos : ∀ i, 0 < hH.eigenvalues i`. Introduce `i`. Establish `h0 : 0 ≤ hH.eigenvalues i` using `hP.eigenvalues_nonneg i`. Establish `hne : hH.eigenvalues i ≠ 0`. Introduce `h`.

Apply `hd` to reduce the goal to its premises. Rewrite using `[hH.det_eq_prod_eigenvalues]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])`. Conclude with `lt_of_le_of_ne h0 (Ne.symm hne)`. Take `⟨U, hU⟩ : ∃ U : Matrix (Fin n) (Fin n) ℂ, U = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)` from `⟨_, rfl⟩`.

Establish `hUU : star U * U = 1`. Rewrite using `[hU, ← Unitary.coe_star]`. Conclude with `Unitary.coe_star_mul_self _`. Establish `hspec : S = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U`. Establish `h` using `hH.spectral_theorem`.

Rewrite `h` using `[Unitary.conjStarAlgAut_apply]`. Rewrite using `[hU]`. Conclude with `h`. Take `⟨Dm, hDm⟩ : ∃ Dm : Matrix (Fin n) (Fin n) ℂ, Dm = diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ))` from `⟨_, rfl⟩`. Use `⟨Dm * star U, ?_⟩` and prove the remaining obligations.

Establish `hTh : (Dm * star U)ᴴ = U * Dm`. Rewrite using `[conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose, hDm, diagonal_conjTranspose]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Rewrite using `[hTh, hspec]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by`. Rewrite using `[hUU, Matrix.mul_one, Matrix.mul_one, hDm, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `hl` using `hpos i`. Establish `hs : Real.sqrt (hH.eigenvalues i) ^ 2 = hH.eigenvalues i` using `Real.sq_sqrt hl.le`. Simplify using `only [Function.comp_apply]`.

Establish `e : (RCLike.ofReal (hH.eigenvalues i) : ℂ) = ((hH.eigenvalues i : ℝ) : ℂ)` using `rfl`. Rewrite using `[e, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]`. Use `congr 1`. Rewrite using `[mul_comm ((Real.sqrt (hH.eigenvalues i))⁻¹) (hH.eigenvalues i), mul_assoc, ← sq, inv_pow, hs, mul_inv_cancel₀ hl.ne']`.
-/
lemma exists_normalizer {S : Matrix (Fin n) (Fin n) ℂ} (hH : S.IsHermitian) (hP : S.PosSemidef)
    (hd : S.det ≠ 0) : ∃ T : Matrix (Fin n) (Fin n) ℂ, T * S * Tᴴ = 1 := by
  classical
  have hpos : ∀ i, 0 < hH.eigenvalues i := by
    intro i
    have h0 : 0 ≤ hH.eigenvalues i := hP.eigenvalues_nonneg i
    have hne : hH.eigenvalues i ≠ 0 := by
      intro h
      apply hd
      rw [hH.det_eq_prod_eigenvalues]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])
    exact lt_of_le_of_ne h0 (Ne.symm hne)
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin n) (Fin n) ℂ, U = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) :=
    ⟨_, rfl⟩
  have hUU : star U * U = 1 := by
    rw [hU, ← Unitary.coe_star]; exact Unitary.coe_star_mul_self _
  have hspec : S = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hU]; exact h
  obtain ⟨Dm, hDm⟩ : ∃ Dm : Matrix (Fin n) (Fin n) ℂ,
      Dm = diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) := ⟨_, rfl⟩
  refine ⟨Dm * star U, ?_⟩
  have hTh : (Dm * star U)ᴴ = U * Dm := by
    rw [conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose, hDm, diagonal_conjTranspose]
    congr 2
    funext i
    simp
  rw [hTh, hspec]
  calc Dm * star U * (U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U) * (U * Dm)
      = Dm * (star U * U) * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * (star U * U) * Dm := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [hUU, Matrix.mul_one, Matrix.mul_one, hDm, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      have hl := hpos i
      have hs : Real.sqrt (hH.eigenvalues i) ^ 2 = hH.eigenvalues i := Real.sq_sqrt hl.le
      simp only [Function.comp_apply]
      have e : (RCLike.ofReal (hH.eigenvalues i) : ℂ) = ((hH.eigenvalues i : ℝ) : ℂ) := rfl
      rw [e, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
      congr 1
      rw [mul_comm ((Real.sqrt (hH.eigenvalues i))⁻¹) (hH.eigenvalues i), mul_assoc, ← sq, inv_pow, hs,
        mul_inv_cancel₀ hl.ne']

/- English proof (translation)
Take `⟨A, B, C, Dm, hY⟩ : ∃ A B C Dm : Matrix (Fin n) (Fin n) ℂ, mR y = fromBlocks A B C Dm` from `⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩`. Establish `hYG : InG (mR y)` using `y.2`. Establish `hYJ : mR y * JJ n * (mR y)ᴴ = JJ n` using `conj_jj y.1.isUnit hYG`. Rewrite `hYJ` using `[hY]`. Take `⟨hCD, hAB⟩` from `rows_rel hYJ`.

Establish `hSH : (C * Cᴴ + Dm * Dmᴴ).IsHermitian` using `(isHermitian_mul_conjTranspose_self C).add (isHermitian_mul_conjTranspose_self Dm)`. Establish `hSP : (C * Cᴴ + Dm * Dmᴴ).PosSemidef` using `(posSemidef_self_mul_conjTranspose C).add (posSemidef_self_mul_conjTranspose Dm)`. Take `⟨T, hT⟩` from `exists_normalizer hSH hSP (det_S_ne hAB)`. Establish `hN : (T * C) * (T * C)ᴴ + (T * Dm) * (T * Dm)ᴴ = 1`. Rewrite using `[← hT, conjTranspose_mul, conjTranspose_mul]`.

Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`. Establish `hI' : (T * C) * (T * Dm)ᴴ = (T * Dm) * (T * C)ᴴ`. Rewrite using `[conjTranspose_mul, conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc C, hCD, Matrix.mul_assoc]`.

Establish `hBL : C * (T * Dm)ᴴ = Dm * (T * C)ᴴ`. Rewrite using `[conjTranspose_mul, conjTranspose_mul, ← Matrix.mul_assoc, hCD, Matrix.mul_assoc]`. Take `⟨C', hC'⟩ : ∃ C' : Matrix (Fin n) (Fin n) ℂ, C' = T * C` from `⟨_, rfl⟩`. Take `⟨D', hD'⟩ : ∃ D' : Matrix (Fin n) (Fin n) ℂ, D' = T * Dm` from `⟨_, rfl⟩`. Rewrite `hN`, `hI'`, `hBL` using `[← hC', ← hD']`.

Take `⟨K0, hK0⟩ : ∃ K0 : M2 n, K0 = fromBlocks D' (-C') C' D'` from `⟨_, rfl⟩`. Establish `hKK : K0 * K0ᴴ = 1`. Rewrite using `[hK0, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]`. Simplify using `only [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]`. Rewrite using `[fromBlocks_inj]`.

Use `⟨by rw [add_comm]; exact hN, by rw [hI']; exact add_neg_cancel _, by rw [hI']; exact add_neg_cancel _, hN⟩` and prove the remaining obligations. Establish `hKK' : K0ᴴ * K0 = 1` using `mul_eq_one_comm.mp hKK`. Establish `hJK : JJ n * K0 = K0 * JJ n`. Rewrite using `[hK0]`. Simplify using `[JJ, fromBlocks_multiply]`.

Establish `hKG : K0ᴴ * JJ n * K0 = JJ n`. Rewrite using `[Matrix.mul_assoc, hJK, ← Matrix.mul_assoc, hKK', Matrix.one_mul]`. Set `u : (M2 n)ˣ` to `⟨K0, K0ᴴ, hKK, hKK'⟩`. Set `kG : GR n` to `⟨u, hKG⟩`. Establish `hkK : InK (mR kG)` using `⟨hKG, hKK'⟩`.

Take `⟨q, hq⟩ : ∃ q : GR n, q = y * kG⁻¹` from `⟨_, rfl⟩`. Establish `hyq : y = q * kG` using `by rw [hq, inv_mul_cancel_right]`. Establish `hmq : mR q = mR y * K0ᴴ` using `by rw [hq]; rfl`. Establish `h21 : (mR q).toBlocks₂₁ = 0`. Rewrite using `[hmq, hY, hK0, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₁, conjTranspose_neg, Matrix.mul_neg, hBL, add_neg_cancel]`.

Use `⟨q, kG, hyq, h21, hkK, ?_⟩` and prove the remaining obligations. Rewrite using `[hyq]`. Conclude with `hLoc_mul q kG h21 hkK`.
-/
theorem locIwasawa (y : GR n) : ∃ q k₀ : GR n, y = q * k₀ ∧ (mR q).toBlocks₂₁ = 0 ∧ InK (mR k₀) ∧
    hLoc y = ‖(mR q).toBlocks₁₁.det‖ ^ 2 := by
  classical
  obtain ⟨A, B, C, Dm, hY⟩ : ∃ A B C Dm : Matrix (Fin n) (Fin n) ℂ, mR y = fromBlocks A B C Dm :=
    ⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩
  have hYG : InG (mR y) := y.2
  have hYJ : mR y * JJ n * (mR y)ᴴ = JJ n := conj_jj y.1.isUnit hYG
  rw [hY] at hYJ
  obtain ⟨hCD, hAB⟩ := rows_rel hYJ
  have hSH : (C * Cᴴ + Dm * Dmᴴ).IsHermitian :=
    (isHermitian_mul_conjTranspose_self C).add (isHermitian_mul_conjTranspose_self Dm)
  have hSP : (C * Cᴴ + Dm * Dmᴴ).PosSemidef :=
    (posSemidef_self_mul_conjTranspose C).add (posSemidef_self_mul_conjTranspose Dm)
  obtain ⟨T, hT⟩ := exists_normalizer hSH hSP (det_S_ne hAB)
  have hN : (T * C) * (T * C)ᴴ + (T * Dm) * (T * Dm)ᴴ = 1 := by
    rw [← hT, conjTranspose_mul, conjTranspose_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have hI' : (T * C) * (T * Dm)ᴴ = (T * Dm) * (T * C)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc C, hCD, Matrix.mul_assoc]
  have hBL : C * (T * Dm)ᴴ = Dm * (T * C)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, ← Matrix.mul_assoc, hCD, Matrix.mul_assoc]
  obtain ⟨C', hC'⟩ : ∃ C' : Matrix (Fin n) (Fin n) ℂ, C' = T * C := ⟨_, rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : Matrix (Fin n) (Fin n) ℂ, D' = T * Dm := ⟨_, rfl⟩
  rw [← hC', ← hD'] at hN hI' hBL
  obtain ⟨K0, hK0⟩ : ∃ K0 : M2 n, K0 = fromBlocks D' (-C') C' D' := ⟨_, rfl⟩
  have hKK : K0 * K0ᴴ = 1 := by
    rw [hK0, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]
    simp only [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    rw [fromBlocks_inj]
    refine ⟨by rw [add_comm]; exact hN, by rw [hI']; exact add_neg_cancel _, by rw [hI']; exact add_neg_cancel _, hN⟩
  have hKK' : K0ᴴ * K0 = 1 := mul_eq_one_comm.mp hKK
  have hJK : JJ n * K0 = K0 * JJ n := by
    rw [hK0]
    simp [JJ, fromBlocks_multiply]
  have hKG : K0ᴴ * JJ n * K0 = JJ n := by
    rw [Matrix.mul_assoc, hJK, ← Matrix.mul_assoc, hKK', Matrix.one_mul]
  let u : (M2 n)ˣ := ⟨K0, K0ᴴ, hKK, hKK'⟩
  let kG : GR n := ⟨u, hKG⟩
  have hkK : InK (mR kG) := ⟨hKG, hKK'⟩
  obtain ⟨q, hq⟩ : ∃ q : GR n, q = y * kG⁻¹ := ⟨_, rfl⟩
  have hyq : y = q * kG := by rw [hq, inv_mul_cancel_right]
  have hmq : mR q = mR y * K0ᴴ := by rw [hq]; rfl
  have h21 : (mR q).toBlocks₂₁ = 0 := by
    rw [hmq, hY, hK0, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₁, conjTranspose_neg,
      Matrix.mul_neg, hBL, add_neg_cancel]
  refine ⟨q, kG, hyq, h21, hkK, ?_⟩
  rw [hyq]
  exact hLoc_mul q kG h21 hkK

end PositivityTheory.Rg.Sw.Glob
