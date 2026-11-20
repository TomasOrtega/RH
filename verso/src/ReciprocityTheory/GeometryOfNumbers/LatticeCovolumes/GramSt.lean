import Mathlib

namespace ReciprocityTheory.GeometryOfNumbersTheory

open Matrix
open scoped ComplexOrder MatrixOrder

section SlopeTestRemainingChoices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use `set U := hQ.1.eigenvectorUnitary`. Establish `hspec` using `hQ.1.spectral_theorem`. Establish `h1 : (1 + Q) = Unitary.conjStarAlgAut ℂ _ U (1 + diagonal (RCLike.ofReal ∘ hQ.1.eigenvalues))`. Rewrite using `[map_add, map_one, ← hspec]`. Establish `hd : (1 + diagonal (RCLike.ofReal ∘ hQ.1.eigenvalues) : Matrix ι ι ℂ) = diagonal (fun i => ((1 + hQ.1.eigenvalues i : ℝ) : ℂ))`.

Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, one_apply]`.

Rewrite using `[h1, Unitary.conjStarAlgAut_apply, hd, det_mul, det_mul, det_diagonal, Complex.ofReal_prod]`. Rewrite using `[mul_comm (det _) (∏ _, _), mul_assoc, ← det_mul]`. Apply the tactic sequence `try rw [Unitary.coe_star]`. Rewrite using `[Unitary.mul_star_self_of_mem U.2, det_one, mul_one]`.
-/
theorem gramSt_det_one_add_eq {Q : Matrix ι ι ℂ} (hQ : Q.PosSemidef) :
    (1 + Q).det = ((∏ i, (1 + hQ.1.eigenvalues i) : ℝ) : ℂ) := by
  set U := hQ.1.eigenvectorUnitary
  have hspec := hQ.1.spectral_theorem
  have h1 : (1 + Q) = Unitary.conjStarAlgAut ℂ _ U
      (1 + diagonal (RCLike.ofReal ∘ hQ.1.eigenvalues)) := by
    rw [map_add, map_one, ← hspec]
  have hd : (1 + diagonal (RCLike.ofReal ∘ hQ.1.eigenvalues) : Matrix ι ι ℂ) =
      diagonal (fun i => ((1 + hQ.1.eigenvalues i : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h, one_apply]
  rw [h1, Unitary.conjStarAlgAut_apply, hd, det_mul, det_mul, det_diagonal, Complex.ofReal_prod]
  rw [mul_comm (det _) (∏ _, _), mul_assoc, ← det_mul]
  try rw [Unitary.coe_star]
  rw [Unitary.mul_star_self_of_mem U.2, det_one, mul_one]

/- English proof (translation)
Use `set S := CFC.sqrt G with hSdef`. Establish `hS0 : S.PosSemidef` using `(CFC.sqrt_nonneg G).posSemidef`. Establish `hSS : S * S = G` using `CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg`. Establish `hSh : Sᴴ = S` using `hS0.1`. Establish `hdetG : G.det = S.det * S.det` using `by rw [← hSS, det_mul]`.

Establish `hGpos` using `hG.det_pos`. Establish `hSdet : S.det ≠ 0`. Introduce `h`. Rewrite `hGpos` using `[hdetG, h, zero_mul]`. Conclude with `lt_irrefl _ hGpos`.

Establish `hSu : IsUnit S.det` using `isUnit_iff_ne_zero.mpr hSdet`. Establish `hQ : (S⁻¹ * (H - G) * (S⁻¹)ᴴ).PosSemidef` using `hGH.mul_mul_conjTranspose_same _`. Establish `hinvh : (S⁻¹)ᴴ = S⁻¹` using `by rw [conjTranspose_nonsing_inv, hSh]`. Establish `h2 : S * (S⁻¹ * (H - G) * (S⁻¹)ᴴ) * S = H - G`. Rewrite using `[hinvh, show S * (S⁻¹ * (H - G) * S⁻¹) * S = (S * S⁻¹) * (H - G) * (S⁻¹ * S) by`.

Simplify using `only [Matrix.mul_assoc]]`. Rewrite using `[mul_nonsing_inv S hSu, nonsing_inv_mul S hSu, Matrix.one_mul, Matrix.mul_one]`. Establish `hH : H = S * (1 + S⁻¹ * (H - G) * (S⁻¹)ᴴ) * S`. Rewrite using `[Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hSS, h2]`. Normalize the expressions using the abelian group laws.

Establish `hdetH : H.det = G.det * (1 + S⁻¹ * (H - G) * (S⁻¹)ᴴ).det` using `by conv_lhs => rw [hH]`. Rewrite using `[det_mul, det_mul, hdetG]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hdetH, gramSt_det_one_add_eq hQ]`. Take `⟨hre, him⟩` from `Complex.pos_iff.mp hGpos`.

Rewrite using `[Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]`. Establish `h1 : (1:ℝ) ≤ ∏ i, (1 + hQ.1.eigenvalues i)`. Combine the equalities or inequalities in the displayed calculation. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gramSt_det_re_le_of_sub {G H : Matrix ι ι ℂ} (hG : G.PosDef)
    (hGH : (H - G).PosSemidef) : G.det.re ≤ H.det.re := by
  set S := CFC.sqrt G with hSdef
  have hS0 : S.PosSemidef := (CFC.sqrt_nonneg G).posSemidef
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hSh : Sᴴ = S := hS0.1
  have hdetG : G.det = S.det * S.det := by rw [← hSS, det_mul]
  have hGpos := hG.det_pos
  have hSdet : S.det ≠ 0 := by
    intro h; rw [hdetG, h, zero_mul] at hGpos; exact lt_irrefl _ hGpos
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet
  have hQ : (S⁻¹ * (H - G) * (S⁻¹)ᴴ).PosSemidef := hGH.mul_mul_conjTranspose_same _
  have hinvh : (S⁻¹)ᴴ = S⁻¹ := by rw [conjTranspose_nonsing_inv, hSh]
  have h2 : S * (S⁻¹ * (H - G) * (S⁻¹)ᴴ) * S = H - G := by
    rw [hinvh, show S * (S⁻¹ * (H - G) * S⁻¹) * S = (S * S⁻¹) * (H - G) * (S⁻¹ * S) by
      simp only [Matrix.mul_assoc]]
    rw [mul_nonsing_inv S hSu, nonsing_inv_mul S hSu, Matrix.one_mul, Matrix.mul_one]
  have hH : H = S * (1 + S⁻¹ * (H - G) * (S⁻¹)ᴴ) * S := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hSS, h2]; abel
  have hdetH : H.det = G.det * (1 + S⁻¹ * (H - G) * (S⁻¹)ᴴ).det := by
    conv_lhs => rw [hH]
    rw [det_mul, det_mul, hdetG]; ring
  rw [hdetH, gramSt_det_one_add_eq hQ]
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hGpos
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have h1 : (1:ℝ) ≤ ∏ i, (1 + hQ.1.eigenvalues i) := by
    calc (1:ℝ) = ∏ _i : ι, (1:ℝ) := by simp
      _ ≤ ∏ i, (1 + hQ.1.eigenvalues i) :=
        Finset.prod_le_prod (fun _ _ => zero_le_one)
          (fun i _ => by linarith [hQ.eigenvalues_nonneg i])
  nlinarith

end SlopeTestRemainingChoices

section Block

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

/- English proof (translation)
Establish `hA : A.PosDef`. Use `h.submatrix (e := (Sum.inl : m → m ⊕ k)) Sum.inl_injective` as an intermediate fact. Establish `e : (fromBlocks A B C D).submatrix Sum.inl Sum.inl = A` using `by ext; simp`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `hD : D.PosDef`.

Use `h.submatrix (e := (Sum.inr : k → m ⊕ k)) Sum.inr_injective` as an intermediate fact. Establish `e : (fromBlocks A B C D).submatrix Sum.inr Sum.inr = D` using `by ext; simp`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `hC : C = Bᴴ`. Use `(isHermitian_fromBlocks_iff.mp h.1)` as an intermediate fact.

Conclude with `this.2.1.symm`. Substitute `hC` using the available equality. Establish `: Invertible A` using `hA.isUnit.invertible`. Establish `hS : (D - Bᴴ * A⁻¹ * B).PosSemidef` using `(PosDef.fromBlocks₁₁ B D hA).mp h.posSemidef`. Establish `hdet : (fromBlocks A B Bᴴ D).det = A.det * (D - Bᴴ * A⁻¹ * B).det`.

Rewrite using `[det_fromBlocks₁₁, invOf_eq_nonsing_inv]`. Establish `hSne : (D - Bᴴ * A⁻¹ * B).det ≠ 0`. Introduce `h0`. Use `h.det_pos` as an intermediate fact. Rewrite `this` using `[hdet, h0, mul_zero]`.

Conclude with `lt_irrefl _ this`. Establish `hSd : (D - Bᴴ * A⁻¹ * B).PosDef` using `hS.posDef_iff_det_ne_zero.mpr hSne`. Establish `hdiff : (D - (D - Bᴴ * A⁻¹ * B)).PosSemidef`. Rewrite using `[sub_sub_cancel]`. Conclude with `hA.inv.posSemidef.conjTranspose_mul_mul_same B`.

Establish `hmono` using `gramSt_det_re_le_of_sub hSd hdiff`. Take `⟨hAre, hAim⟩` from `Complex.pos_iff.mp hA.det_pos`. Rewrite using `[hdet, Complex.mul_re, ← hAim, zero_mul, sub_zero]`. Conclude with `mul_le_mul_of_nonneg_left hmono hAre.le`.
-/
theorem gramSt_fischer {A : Matrix m m ℂ} {B : Matrix m k ℂ} {C : Matrix k m ℂ} {D : Matrix k k ℂ}
    (h : (fromBlocks A B C D).PosDef) :
    (fromBlocks A B C D).det.re ≤ A.det.re * D.det.re := by
  have hA : A.PosDef := by
    have := h.submatrix (e := (Sum.inl : m → m ⊕ k)) Sum.inl_injective
    have e : (fromBlocks A B C D).submatrix Sum.inl Sum.inl = A := by ext; simp
    rwa [e] at this
  have hD : D.PosDef := by
    have := h.submatrix (e := (Sum.inr : k → m ⊕ k)) Sum.inr_injective
    have e : (fromBlocks A B C D).submatrix Sum.inr Sum.inr = D := by ext; simp
    rwa [e] at this
  have hC : C = Bᴴ := by
    have := (isHermitian_fromBlocks_iff.mp h.1)
    exact this.2.1.symm
  subst hC
  have : Invertible A := hA.isUnit.invertible
  have hS : (D - Bᴴ * A⁻¹ * B).PosSemidef :=
    (PosDef.fromBlocks₁₁ B D hA).mp h.posSemidef
  have hdet : (fromBlocks A B Bᴴ D).det = A.det * (D - Bᴴ * A⁻¹ * B).det := by
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hSne : (D - Bᴴ * A⁻¹ * B).det ≠ 0 := by
    intro h0
    have := h.det_pos
    rw [hdet, h0, mul_zero] at this
    exact lt_irrefl _ this
  have hSd : (D - Bᴴ * A⁻¹ * B).PosDef := hS.posDef_iff_det_ne_zero.mpr hSne
  have hdiff : (D - (D - Bᴴ * A⁻¹ * B)).PosSemidef := by
    rw [sub_sub_cancel]
    exact hA.inv.posSemidef.conjTranspose_mul_mul_same B
  have hmono := gramSt_det_re_le_of_sub hSd hdiff
  obtain ⟨hAre, hAim⟩ := Complex.pos_iff.mp hA.det_pos
  rw [hdet, Complex.mul_re, ← hAim, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left hmono hAre.le

end Block

/- English proof (translation)
Establish `hE : M.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks (M.submatrix (Fin.castAdd b) (Fin.castAdd b)) (M.submatrix (Fin.castAdd b) (Fin.natAdd a)) (M.submatrix (Fin.natAdd a) (Fin.castAdd b)) (M.submatrix (Fin.natAdd a) (Fin.natAdd a))`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp`. Establish `hP : (M.submatrix finSumFinEquiv finSumFinEquiv).PosDef` using `hM.submatrix finSumFinEquiv.injective`. Rewrite `hP` using `[hE]`. Use `gramSt_fischer hP` as an intermediate fact.

Rewrite `this` using `[← hE, det_submatrix_equiv_self]`. Then use the resulting hypothesis.
-/
theorem gramSt_fin_blocks {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ} (hM : M.PosDef) :
    M.det.re ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re *
      (M.submatrix (Fin.natAdd a) (Fin.natAdd a)).det.re := by
  have hE : M.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (M.submatrix (Fin.castAdd b) (Fin.castAdd b))
        (M.submatrix (Fin.castAdd b) (Fin.natAdd a))
        (M.submatrix (Fin.natAdd a) (Fin.castAdd b))
        (M.submatrix (Fin.natAdd a) (Fin.natAdd a)) := by
    ext (i | i) (j | j) <;> simp
  have hP : (M.submatrix finSumFinEquiv finSumFinEquiv).PosDef :=
    hM.submatrix finSumFinEquiv.injective
  rw [hE] at hP
  have := gramSt_fischer hP
  rwa [← hE, det_submatrix_equiv_self] at this

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `h1` using `gramSt_fin_blocks (a := k) (b := 1) hD`. Establish `h2` using `ih (hD.submatrix (Fin.castAdd_injective k 1))`.

Establish `h3 : (D.submatrix (Fin.natAdd k) (Fin.natAdd k : Fin 1 → Fin (k + 1))).det = D (Fin.last k) (Fin.last k)`. Rewrite using `[det_unique]`. Both sides reduce to the same expression. Establish `h4 : 0 ≤ (D (Fin.last k) (Fin.last k)).re` using `(Complex.pos_iff.mp hD.diag_pos).1.le`. Rewrite `h1` using `[h3]`.

Rewrite using `[Fin.prod_univ_castSucc]`. Conclude with `h1.trans (mul_le_mul_of_nonneg_right h2 h4)`.
-/
theorem gramSt_hadamard {k : ℕ} {D : Matrix (Fin k) (Fin k) ℂ} (hD : D.PosDef) :
    D.det.re ≤ ∏ j : Fin k, (D j j).re := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := gramSt_fin_blocks (a := k) (b := 1) hD
    have h2 := ih (hD.submatrix (Fin.castAdd_injective k 1))
    have h3 : (D.submatrix (Fin.natAdd k) (Fin.natAdd k : Fin 1 → Fin (k + 1))).det =
        D (Fin.last k) (Fin.last k) := by
      rw [det_unique]; rfl
    have h4 : 0 ≤ (D (Fin.last k) (Fin.last k)).re := (Complex.pos_iff.mp hD.diag_pos).1.le
    rw [h3] at h1
    rw [Fin.prod_univ_castSucc]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 h4)

/- English proof (translation)
Take `⟨h1, h2⟩` from `Complex.pos_iff.mp hG.det_pos`. Conclude with `⟨h1, h2.symm⟩`.
-/
theorem posDef_det_re_pos {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) :
    0 < G.det.re ∧ G.det.im = 0 := by
  obtain ⟨h1, h2⟩ := Complex.pos_iff.mp hG.det_pos
  exact ⟨h1, h2.symm⟩

/- English proof (translation)
The claim follows from `gramSt_det_re_le_of_sub hG hGH`.
-/
theorem det_re_le_of_sub_posSemidef {n : ℕ} {G H : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (hGH : (H - G).PosSemidef) : G.det.re ≤ H.det.re :=
  gramSt_det_re_le_of_sub hG hGH

/- English proof (translation)
Establish `h1` using `gramSt_fin_blocks hM`. Establish `h2` using `gramSt_hadamard (hM.submatrix (e := Fin.natAdd a) (Fin.natAdd_injective b a))`. Establish `h0 : 0 ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re` using `(Complex.pos_iff.mp (hM.submatrix (Fin.castAdd_injective a b)).det_pos).1.le`. Conclude with `h1.trans (mul_le_mul_of_nonneg_left h2 h0)`.
-/
theorem det_re_le_mul_prod_diag {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hM : M.PosDef) :
    M.det.re ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re *
      ∏ j : Fin b, (M (Fin.natAdd a j) (Fin.natAdd a j)).re := by
  have h1 := gramSt_fin_blocks hM
  have h2 := gramSt_hadamard (hM.submatrix (e := Fin.natAdd a) (Fin.natAdd_injective b a))
  have h0 : 0 ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re :=
    (Complex.pos_iff.mp (hM.submatrix (Fin.castAdd_injective a b)).det_pos).1.le
  exact h1.trans (mul_le_mul_of_nonneg_left h2 h0)

end ReciprocityTheory.GeometryOfNumbersTheory
