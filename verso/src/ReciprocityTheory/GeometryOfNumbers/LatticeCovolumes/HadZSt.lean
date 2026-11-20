import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.GramSt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.HadZStA

namespace ReciprocityTheory.GeometryOfNumbersTheory

open Matrix
open scoped ComplexOrder

/- English proof (translation)
Establish `hu0 : LinearIndependent ℚ (M.map (Int.cast : ℤ → ℚ)).col` using `Matrix.mulVec_injective_iff.mp hM`. Establish `hNq : (N.map (Int.cast : ℤ → ℚ)).det ≠ 0`. Rewrite using `[← Int.cast_det]`. Conclude with `hN` after adjusting the coercions. Establish `hw : LinearIndependent ℚ (N.map (Int.cast : ℤ → ℚ)).col` using `Matrix.linearIndependent_cols_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hNq.isUnit)`.

Take `⟨m, f, hmr, hLI⟩` from `LinearIndependentExtension.exists_append_li _ hu0 _ hw`. Substitute `hmr` using the available equality. Use `set U : Matrix (Fin (r' + m)) (Fin (r' + m)) ℤ := Matrix.of fun i j => Fin.append (fun k => M i k) (fun k => N i (f k)) j with hUdef`. Establish `hUq : (U.map (Int.cast : ℤ → ℚ)).col = Fin.append (M.map (Int.cast : ℤ → ℚ)).col ((N.map (Int.cast : ℤ → ℚ)).col ∘ f)`. Use function extensionality and compare the values at `j i`.

Use `Fin.addCases (fun k => ?_) (fun k => ?_) j` and prove the remaining obligations. Rewrite using `[Fin.append_left]`. Simplify using `[U, Matrix.col]`. Rewrite using `[Fin.append_right]`. Simplify using `[U, Matrix.col]`.

Both sides reduce to the same expression. Establish `hUdet : U.det ≠ 0`. Rewrite `hLI` using `[← hUq, Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← Int.cast_det]`. Conclude with `hLI` after adjusting the coercions. Use `set UC := U.map (Int.cast : ℤ → ℂ) with hUC`.

Use `set MC := M.map (Int.cast : ℤ → ℂ) with hMC`. Use `set NC := N.map (Int.cast : ℤ → ℂ) with hNC`. Establish `hUCdet : UC.det = ((U.det : ℤ) : ℂ)` using `by rw [hUC, Int.cast_det]`. Establish `hUCinj : Function.Injective UC.mulVec`. Rewrite using `[Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, hUCdet, isUnit_iff_ne_zero]`.

Conclude with `hUdet` after adjusting the coercions. Use `set H := UCᴴ * G * UC with hH`. Establish `hHpd : H.PosDef` using `hG.conjTranspose_mul_mul_same hUCinj`. Establish `hUl : ∀ l i, UC l (Fin.castAdd m i) = MC l i` using `by intro l i; simp [UC, U, MC]`. Establish `hUr : ∀ l j, UC l (Fin.natAdd r' j) = NC l (f j)` using `by intro l j; simp [UC, U, NC]`.

Establish `hsub : H.submatrix (Fin.castAdd m) (Fin.castAdd m) = MCᴴ * G * MC`. Use extensionality with `i j`. Simplify using `only [H, submatrix_apply, mul_apply, conjTranspose_apply, hUl]`. Establish `hdiag : ∀ j, H (Fin.natAdd r' j) (Fin.natAdd r' j) = (NCᴴ * G * NC) (f j) (f j)`. Introduce `j`.

Simplify using `only [H, mul_apply, conjTranspose_apply, hUr]`. Establish `hMMpd : (MCᴴ * G * MC).PosDef`. Rewrite using `[← hsub]`. Conclude with `hHpd.submatrix (Fin.castAdd_injective r' m)`. Establish `hdetH : H.det.re = ((U.det : ℝ) ^ 2) * G.det.re`.

Rewrite using `[hH, det_mul, det_mul, det_conjTranspose, hUCdet]`. Simplify using `[Complex.mul_re, Complex.mul_im, sq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd1 : (1 : ℝ) ≤ (U.det : ℝ) ^ 2`. Establish `h1` using `Int.one_le_abs hUdet`.

Establish `: (1 : ℤ) ≤ U.det ^ 2` using `by nlinarith [sq_abs U.det]`. Conclude with `this` after adjusting the coercions. Establish `hGpos` using `(posDef_det_re_pos hG).1`. Establish `hG'pos` using `(posDef_det_re_pos hG').1`. Establish `hstep1 : G.det.re ≤ H.det.re` using `by rw [hdetH]; nlinarith`.

Establish `hstep2` using `det_re_le_mul_prod_diag hHpd`. Rewrite `hstep2` using `[hsub]`. Establish `hprod : ∏ j : Fin m, (H (Fin.natAdd r' j) (Fin.natAdd r' j)).re ≤ (lam ^ 2) ^ m`. Rewrite using `[← Fin.prod_const]`. Use `Finset.prod_le_prod (fun j _ => (Complex.pos_iff.mp (hHpd.diag_pos)).1.le) (fun j _ => ?_)` and prove the remaining obligations.

Rewrite using `[hdiag]`. Conclude with `hsmall _`. Establish `hMM : (MCᴴ * G * MC).det.re ≤ (A ^ 2) ^ r' * G'.det.re`. Use `det_re_le_of_sub_posSemidef hMMpd hnorm` as an intermediate fact. Rewrite `this` using `[det_smul, Fintype.card_fin]`.

Establish `e : ((A : ℂ) ^ 2) ^ r' = (((A ^ 2) ^ r' : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite `this` using `[e, Complex.re_ofReal_mul]`. Then use the resulting hypothesis. Establish `hMMpos` using `(posDef_det_re_pos hMMpd).1`. Establish `hfin : G.det.re ≤ (A ^ 2) ^ r' * G'.det.re * (lam ^ 2) ^ m`. Establish `hP0 : 0 ≤ ∏ j : Fin m, (H (Fin.natAdd r' j) (Fin.natAdd r' j)).re` using `Finset.prod_nonneg fun j _ => (Complex.pos_iff.mp (hHpd.diag_pos)).1.le`.

Combine the equalities or inequalities in the displayed calculation. Establish `hlog` using `Real.log_le_log hGpos hfin`. Rewrite `hlog` using `[Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]`. Move the coercions through the operations in `at hlog ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem neg_log_det_le {r' r : ℕ} (hr : r' ≤ r) {G' : Matrix (Fin r') (Fin r') ℂ}
    {G : Matrix (Fin r) (Fin r) ℂ} (hG' : G'.PosDef) (hG : G.PosDef)
    (M : Matrix (Fin r) (Fin r') ℤ) (hM : Function.Injective (M.map (Int.cast : ℤ → ℚ)).mulVec)
    (N : Matrix (Fin r) (Fin r) ℤ) (hN : N.det ≠ 0) {A lam : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hnorm : (((A : ℂ) ^ 2) • G' -
      (M.map (Int.cast : ℤ → ℂ))ᴴ * G * M.map (Int.cast : ℤ → ℂ)).PosSemidef)
    (hsmall : ∀ i, (((N.map (Int.cast : ℤ → ℂ))ᴴ * G * N.map (Int.cast : ℤ → ℂ)) i i).re ≤ lam ^ 2) :
    -(1 / 2) * Real.log G'.det.re ≤
      -(1 / 2) * Real.log G.det.re + r' * Real.log A + ((r : ℝ) - r') * Real.log lam := by
  classical
  have hu0 : LinearIndependent ℚ (M.map (Int.cast : ℤ → ℚ)).col := Matrix.mulVec_injective_iff.mp hM
  have hNq : (N.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [← Int.cast_det]; exact_mod_cast hN
  have hw : LinearIndependent ℚ (N.map (Int.cast : ℤ → ℚ)).col :=
    Matrix.linearIndependent_cols_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hNq.isUnit)
  obtain ⟨m, f, hmr, hLI⟩ := LinearIndependentExtension.exists_append_li _ hu0 _ hw
  subst hmr
  set U : Matrix (Fin (r' + m)) (Fin (r' + m)) ℤ :=
    Matrix.of fun i j => Fin.append (fun k => M i k) (fun k => N i (f k)) j with hUdef
  have hUq : (U.map (Int.cast : ℤ → ℚ)).col =
      Fin.append (M.map (Int.cast : ℤ → ℚ)).col ((N.map (Int.cast : ℤ → ℚ)).col ∘ f) := by
    funext j i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · rw [Fin.append_left]; simp [U, Matrix.col]
    · rw [Fin.append_right]; simp [U, Matrix.col]; rfl
  have hUdet : U.det ≠ 0 := by
    rw [← hUq, Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, ← Int.cast_det] at hLI
    exact_mod_cast hLI
  set UC := U.map (Int.cast : ℤ → ℂ) with hUC
  set MC := M.map (Int.cast : ℤ → ℂ) with hMC
  set NC := N.map (Int.cast : ℤ → ℂ) with hNC
  have hUCdet : UC.det = ((U.det : ℤ) : ℂ) := by rw [hUC, Int.cast_det]
  have hUCinj : Function.Injective UC.mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, hUCdet, isUnit_iff_ne_zero]
    exact_mod_cast hUdet
  set H := UCᴴ * G * UC with hH
  have hHpd : H.PosDef := hG.conjTranspose_mul_mul_same hUCinj
  have hUl : ∀ l i, UC l (Fin.castAdd m i) = MC l i := by intro l i; simp [UC, U, MC]
  have hUr : ∀ l j, UC l (Fin.natAdd r' j) = NC l (f j) := by intro l j; simp [UC, U, NC]
  have hsub : H.submatrix (Fin.castAdd m) (Fin.castAdd m) = MCᴴ * G * MC := by
    ext i j; simp only [H, submatrix_apply, mul_apply, conjTranspose_apply, hUl]
  have hdiag : ∀ j, H (Fin.natAdd r' j) (Fin.natAdd r' j) = (NCᴴ * G * NC) (f j) (f j) := by
    intro j; simp only [H, mul_apply, conjTranspose_apply, hUr]
  have hMMpd : (MCᴴ * G * MC).PosDef := by
    rw [← hsub]; exact hHpd.submatrix (Fin.castAdd_injective r' m)

  have hdetH : H.det.re = ((U.det : ℝ) ^ 2) * G.det.re := by
    rw [hH, det_mul, det_mul, det_conjTranspose, hUCdet]
    simp [Complex.mul_re, Complex.mul_im, sq]
    ring
  have hd1 : (1 : ℝ) ≤ (U.det : ℝ) ^ 2 := by
    have h1 := Int.one_le_abs hUdet
    have : (1 : ℤ) ≤ U.det ^ 2 := by nlinarith [sq_abs U.det]
    exact_mod_cast this
  have hGpos := (posDef_det_re_pos hG).1
  have hG'pos := (posDef_det_re_pos hG').1
  have hstep1 : G.det.re ≤ H.det.re := by rw [hdetH]; nlinarith
  have hstep2 := det_re_le_mul_prod_diag hHpd
  rw [hsub] at hstep2
  have hprod : ∏ j : Fin m, (H (Fin.natAdd r' j) (Fin.natAdd r' j)).re ≤ (lam ^ 2) ^ m := by
    rw [← Fin.prod_const]
    refine Finset.prod_le_prod (fun j _ => (Complex.pos_iff.mp (hHpd.diag_pos)).1.le) (fun j _ => ?_)
    rw [hdiag]; exact hsmall _
  have hMM : (MCᴴ * G * MC).det.re ≤ (A ^ 2) ^ r' * G'.det.re := by
    have := det_re_le_of_sub_posSemidef hMMpd hnorm
    rw [det_smul, Fintype.card_fin] at this
    have e : ((A : ℂ) ^ 2) ^ r' = (((A ^ 2) ^ r' : ℝ) : ℂ) := by push_cast; ring
    rwa [e, Complex.re_ofReal_mul] at this
  have hMMpos := (posDef_det_re_pos hMMpd).1
  have hfin : G.det.re ≤ (A ^ 2) ^ r' * G'.det.re * (lam ^ 2) ^ m := by
    have hP0 : 0 ≤ ∏ j : Fin m, (H (Fin.natAdd r' j) (Fin.natAdd r' j)).re :=
      Finset.prod_nonneg fun j _ => (Complex.pos_iff.mp (hHpd.diag_pos)).1.le
    calc G.det.re ≤ H.det.re := hstep1
      _ ≤ _ := hstep2
      _ ≤ (A ^ 2) ^ r' * G'.det.re * (lam ^ 2) ^ m :=
        mul_le_mul hMM hprod hP0 (by positivity)
  have hlog := Real.log_le_log hGpos hfin
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog ⊢
  linarith

end ReciprocityTheory.GeometryOfNumbersTheory
