import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
  ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg Matrix.det (ho τ)`. Establish `h2 : gram τ.1 X.Gm (mat x0 τ) = (mat x0 τ)ᵀ * gram τ.1 X.Gm 1 * (mat x0 τ).map (starRingEnd ℂ)`. Rewrite using `[← ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, Matrix.one_mul]`. Rewrite `h1` using `[h2, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, zero_mul, Matrix.det_diagonal]`.

Use `(Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm` and prove the remaining obligations. Unfold `sgn`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem det_ne_of_orth {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (τ : X.Ψ) : (mat x0 τ).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (ho τ)
  have h2 : gram τ.1 X.Gm (mat x0 τ) =
      (mat x0 τ)ᵀ * gram τ.1 X.Gm 1 * (mat x0 τ).map (starRingEnd ℂ) := by
    rw [← ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, Matrix.one_mul]
  rw [h2, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, zero_mul,
    Matrix.det_diagonal] at h1
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
  unfold sgn
  split_ifs <;> norm_num

def nM (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := mat (nmat X z) τ

/- English proof (translation)
Establish `h' : ¬ b < a` using `not_lt.2 h.le`. Simplify using `[nM, mat, nmat, h', h.ne]`.
-/
theorem nM_upper (z : V (nd X)) (τ : X.Ψ) {a b : Fin r} (h : a < b) : nM X z τ a b = 0 := by
  have h' : ¬ b < a := not_lt.2 h.le
  simp [nM, mat, nmat, h', h.ne]

/- English proof (translation)
Simplify using `[nM, mat, nmat]`.
-/
theorem nM_diag (z : V (nd X)) (τ : X.Ψ) (a : Fin r) : nM X z τ a a = 1 := by
  simp [nM, mat, nmat]

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular]`. Simplify using `[nM_diag]`. Unfold `Matrix.IsLowerTriangular Matrix.BlockTriangular`. Introduce `i j hij`. Conclude with `nM_upper X z τ (OrderDual.toDual_lt_toDual.1 hij)`.
-/
theorem det_nM (z : V (nd X)) (τ : X.Ψ) : (nM X z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [nM_diag]
  · unfold Matrix.IsLowerTriangular Matrix.BlockTriangular
    intro i j hij
    exact nM_upper X z τ (OrderDual.toDual_lt_toDual.1 hij)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_cpt (x0 : Frame X.Ψ r) (z : V (nd X)) (τ : X.Ψ) :
    mat (cpt X x0 z) τ = mat x0 τ * nM X z τ := rfl

def qI (m : Fin (r - X.p0)) : Fin r := ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩

def n1 (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin X.p0) ℂ :=
  (nM X z τ).submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le)

def Wm (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ :=
  (nM X z τ).submatrix (qI X) (Fin.castLE X.p0_le)

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular]`. Simplify using `[n1, nM_diag]`. Unfold `Matrix.IsLowerTriangular Matrix.BlockTriangular`. Introduce `i j hij`. Establish `hij' : i < j` using `OrderDual.toDual_lt_toDual.1 hij`.

Simplify using `only [n1, Matrix.submatrix_apply]`. Apply `nM_upper X z τ` to reduce the goal to its premises. Rewrite `hij'`, the goal using `[Fin.lt_iff_val_lt_val]`. Simplify using `using hij'`.
-/
theorem det_unipotentFrame_eq_one (z : V (nd X)) (τ : X.Ψ) : (n1 X z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [n1, nM_diag]
  · unfold Matrix.IsLowerTriangular Matrix.BlockTriangular
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    simp only [n1, Matrix.submatrix_apply]
    apply nM_upper X z τ
    rw [Fin.lt_iff_val_lt_val] at hij' ⊢
    simpa using hij'

def Zt (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin (r - X.p0)) ℂ :=
  (Wm X z τ * (n1 X z τ)⁻¹)ᵀ

def Am (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin X.p0) ℂ := 1 - Zt X z τ * (Zt X z τ)ᴴ

/- English proof (translation)
Establish `hr : X.p0 + (r - X.p0) = r` using `by have := X.p0_le; omega`. Rewrite using `[← (finCongr hr).sum_comp, Fin.sum_univ_add]`. Both sides reduce to the same expression.
-/
theorem sum_split (f : Fin r → ℂ) :
    ∑ k, f k = ∑ c : Fin X.p0, f (Fin.castLE X.p0_le c) + ∑ m : Fin (r - X.p0), f (qI X m) := by
  have hr : X.p0 + (r - X.p0) = r := by have := X.p0_le; omega
  rw [← (finCongr hr).sum_comp, Fin.sum_univ_add]
  rfl

/- English proof (translation)
Establish `hg : gram τ.1 X.Gm (mat (cpt X x0 z) τ) = (nM X z τ)ᵀ * Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) * (nM X z τ).map (starRingEnd ℂ)`. Rewrite using `[mat_cpt, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, ho τ]`. Use extensionality with `c d`. Rewrite using `[Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]`. Simplify using `only [Data.gramPos, hg, Matrix.submatrix_apply]`.

Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply, n1, Wm, Matrix.submatrix_apply]`. Rewrite using `[sum_split X, sub_eq_add_neg, ← Finset.sum_neg_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations.

Establish `he : ((Fin.castLE X.p0_le e : Fin r) : ℕ) < X.p0` using `by simp`. Simplify using `[sgn, he]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Establish `hm : ¬ ((qI X m : Fin r) : ℕ) < X.p0` using `by simp [qI]`. Simplify using `[sgn, hm]`.
-/
theorem gramPos_cpt (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) (τ : X.Ψ) :
    X.gramPos (cpt X x0 z) τ =
      (n1 X z τ)ᵀ * (n1 X z τ).map (starRingEnd ℂ) - (Wm X z τ)ᵀ * (Wm X z τ).map (starRingEnd ℂ) := by
  have hg : gram τ.1 X.Gm (mat (cpt X x0 z) τ) = (nM X z τ)ᵀ *
      Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
        (nM X z τ).map (starRingEnd ℂ) := by
    rw [mat_cpt, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, ho τ]
  ext c d
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Data.gramPos, hg, Matrix.submatrix_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply, n1, Wm,
    Matrix.submatrix_apply]
  rw [sum_split X, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun e _ => ?_
    have he : ((Fin.castLE X.p0_le e : Fin r) : ℕ) < X.p0 := by simp
    simp [sgn, he]
  · refine Finset.sum_congr rfl fun m _ => ?_
    have hm : ¬ ((qI X m : Fin r) : ℕ) < X.p0 := by simp [qI]
    simp [sgn, hm]

/- English proof (translation)
Establish `hdet : IsUnit (n1 X z τ).det` using `by rw [det_unipotentFrame_eq_one]; exact isUnit_one`. Unfold `Zt`. Rewrite using `[Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one, Matrix.one_mul]`.
-/
theorem unipotentFrame_transpose_mul (z : V (nd X)) (τ : X.Ψ) : (n1 X z τ)ᵀ * Zt X z τ = (Wm X z τ)ᵀ := by
  have hdet : IsUnit (n1 X z τ).det := by rw [det_unipotentFrame_eq_one]; exact isUnit_one
  unfold Zt
  rw [Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one, Matrix.one_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply]`.
-/
theorem transpose_conj {m n : Type*} (M : Matrix m n ℂ) : (Mᵀ)ᴴ = M.map (starRingEnd ℂ) := by
  ext i j
  simp [Matrix.conjTranspose_apply]

/- English proof (translation)
Rewrite using `[gramPos_cpt X x0 ho z τ, transpose_conj]`. Unfold `Am`. Establish `hW` using `unipotentFrame_transpose_mul X z τ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hW, transpose_conj]`.

Use `_ = (n1 X z τ)ᵀ * (1 - Zt X z τ * (Zt X z τ)ᴴ) * (n1 X z τ).map (starRingEnd ℂ) := by`. Rewrite using `[Matrix.conjTranspose_mul, transpose_conj]`. Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]`.
-/
theorem gramPos_eq (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) (τ : X.Ψ) :
    X.gramPos (cpt X x0 z) τ = (n1 X z τ)ᵀ * Am X z τ * ((n1 X z τ)ᵀ)ᴴ := by
  rw [gramPos_cpt X x0 ho z τ, transpose_conj]
  unfold Am
  have hW := unipotentFrame_transpose_mul X z τ
  calc (n1 X z τ)ᵀ * (n1 X z τ).map (starRingEnd ℂ) - (Wm X z τ)ᵀ * (Wm X z τ).map (starRingEnd ℂ)
      = (n1 X z τ)ᵀ * (n1 X z τ).map (starRingEnd ℂ) -
          ((n1 X z τ)ᵀ * Zt X z τ) * ((n1 X z τ)ᵀ * Zt X z τ)ᴴ := by
        rw [hW, transpose_conj]
    _ = (n1 X z τ)ᵀ * (1 - Zt X z τ * (Zt X z τ)ᴴ) * (n1 X z τ).map (starRingEnd ℂ) := by
        rw [Matrix.conjTranspose_mul, transpose_conj]
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[gramPos_eq X x0 ho z τ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_transpose, det_unipotentFrame_eq_one]`. Simplify using the standard rewrite rules.
-/
theorem det_gramPos (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) (τ : X.Ψ) :
    (X.gramPos (cpt X x0 z) τ).det = (Am X z τ).det := by
  rw [gramPos_eq X x0 ho z τ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    Matrix.det_transpose, det_unipotentFrame_eq_one]
  simp

/- English proof (translation)
Establish `hdx : ∀ τ, (mat (cpt X x0 z) τ).det ≠ 0`. Introduce `τ`. Rewrite using `[mat_cpt, Matrix.det_mul, det_nM, mul_one]`. Conclude with `det_ne_of_orth X ho τ`. Establish `hB : ∀ τ, IsUnit ((n1 X z τ)ᵀ).det`.

Introduce `τ`. Rewrite using `[Matrix.det_transpose, det_unipotentFrame_eq_one]`. Conclude with `isUnit_one`. Prove the components needed by the constructor for the conclusion. Introduce `hz τ`.

Establish `hP` using `Data.gramPos_posDef (X := X) (show cpt X x0 z ∈ X.dom from hz) τ`. Rewrite `hP` using `[gramPos_eq X x0 ho z τ]`. Establish `hC : ((n1 X z τ)ᵀ)⁻¹ * (n1 X z τ)ᵀ = 1` using `Matrix.nonsing_inv_mul _ (hB τ)`. Establish `hA : Am X z τ = ((n1 X z τ)ᵀ)⁻¹ * ((n1 X z τ)ᵀ * Am X z τ * ((n1 X z τ)ᵀ)ᴴ) * (((n1 X z τ)ᵀ)⁻¹)ᴴ`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hA]`. Use `hP.mul_mul_conjTranspose_same ?_` and prove the remaining obligations. Introduce `v w hvw`. Establish `h3` using `congrArg (fun u => Matrix.vecMul u (n1 X z τ)ᵀ) hvw`. Simplify `h3` using `[Matrix.vecMul_vecMul, hC]`.

Introduce `hA show cpt X x0 z ∈ X.dom`. Use `mem_dom_of_gramPos (X := X) (fun τ => ⟨hdx τ, ?_⟩)` and prove the remaining obligations. Rewrite using `[gramPos_eq X x0 ho z τ]`. Use `(hA τ).mul_mul_conjTranspose_same ?_` and prove the remaining obligations. Introduce `v w hvw`.

Establish `h3` using `congrArg (fun u => Matrix.vecMul u ((n1 X z τ)ᵀ)⁻¹) hvw`. Simplify `h3` using `[Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (hB τ)]`.
-/
theorem mem_OmF_iff (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) : z ∈ OmF X x0 ↔ ∀ τ, (Am X z τ).PosDef := by
  have hdx : ∀ τ, (mat (cpt X x0 z) τ).det ≠ 0 := by
    intro τ
    rw [mat_cpt, Matrix.det_mul, det_nM, mul_one]
    exact det_ne_of_orth X ho τ
  have hB : ∀ τ, IsUnit ((n1 X z τ)ᵀ).det := by
    intro τ
    rw [Matrix.det_transpose, det_unipotentFrame_eq_one]
    exact isUnit_one
  constructor
  · intro hz τ
    have hP := Data.gramPos_posDef (X := X) (show cpt X x0 z ∈ X.dom from hz) τ
    rw [gramPos_eq X x0 ho z τ] at hP
    have hC : ((n1 X z τ)ᵀ)⁻¹ * (n1 X z τ)ᵀ = 1 := Matrix.nonsing_inv_mul _ (hB τ)
    have hA : Am X z τ = ((n1 X z τ)ᵀ)⁻¹ * ((n1 X z τ)ᵀ * Am X z τ * ((n1 X z τ)ᵀ)ᴴ) *
        (((n1 X z τ)ᵀ)⁻¹)ᴴ := by
      calc Am X z τ = (((n1 X z τ)ᵀ)⁻¹ * (n1 X z τ)ᵀ) * Am X z τ *
            (((n1 X z τ)ᵀ)⁻¹ * (n1 X z τ)ᵀ)ᴴ := by rw [hC]; simp
        _ = _ := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [hA]
    refine hP.mul_mul_conjTranspose_same ?_
    intro v w hvw
    have h3 := congrArg (fun u => Matrix.vecMul u (n1 X z τ)ᵀ) hvw
    simpa [Matrix.vecMul_vecMul, hC] using h3
  · intro hA
    show cpt X x0 z ∈ X.dom
    refine mem_dom_of_gramPos (X := X) (fun τ => ⟨hdx τ, ?_⟩)
    rw [gramPos_eq X x0 ho z τ]
    refine (hA τ).mul_mul_conjTranspose_same ?_
    intro v w hvw
    have h3 := congrArg (fun u => Matrix.vecMul u ((n1 X z τ)ᵀ)⁻¹) hvw
    simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (hB τ)] using h3

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem leadingMinor_eq_gramDet (x : Frame X.Ψ r) (τ : X.Ψ) :
    dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = (X.gramPos x τ).det := rfl

/- English proof (translation)
Take `⟨h1, h2⟩` from `Complex.pos_iff.1 hc`. Establish `hce : c = (c.re : ℂ)` using `Complex.ext rfl (by simp [← h2])`. Use `conv_lhs => rw [hce]`. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg h1.le]`.
-/
theorem norm_of_pos {c : ℂ} (hc : 0 < c) : ‖c‖ = c.re := by
  obtain ⟨h1, h2⟩ := Complex.pos_iff.1 hc
  have hce : c = (c.re : ℂ) := Complex.ext rfl (by simp [← h2])
  conv_lhs => rw [hce]
  rw [Complex.norm_real, Real.norm_of_nonneg h1.le]

/- English proof (translation)
Unfold `rhF`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[leadingMinor_eq_gramDet, det_gramPos X x0 ho z τ]`.
-/
theorem rhF_eq_sum (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) : rhF X x0 z = -∑ τ, Real.log ‖(Am X z τ).det‖ := by
  unfold rhF
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [leadingMinor_eq_gramDet, det_gramPos X x0 ho z τ]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
