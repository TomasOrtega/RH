import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Use `X.p0_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem signature_add_sub_cancel (X : Data E r) : X.p0 + (r - X.p0) = r := by
  have := X.p0_le
  omega

def eS (X : Data E r) : Fin (r - X.p0) ⊕ Fin X.p0 ≃ Fin r :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (signature_add_sub_cancel X)))

/- English proof (translation)
Simplify using `[eS]`.
-/
theorem eS_inl (X : Data E r) (i : Fin (r - X.p0)) : ((eS X (Sum.inl i)) : ℕ) = X.p0 + i := by
  simp [eS]

/- English proof (translation)
Simplify using `[eS]`.
-/
theorem eS_inr (X : Data E r) (j : Fin X.p0) : ((eS X (Sum.inr j)) : ℕ) = j := by
  simp [eS]

def gM (X : Data E r) (x0 x : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := (mat x0 τ)⁻¹ * mat x τ

def Mq (X : Data E r) (x0 x : Frame X.Ψ r) (τ : X.Ψ) :
    Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ :=
  ((gM X x0 x τ).map (starRingEnd ℂ)).submatrix (eS X) (eS X)

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `rcases a with i | j <;> rcases b with k | l <;>`. Simplify using `[Jd, Jf, Matrix.diagonal_apply, Matrix.one_apply, sgn, eS_inl, eS_inr, Equiv.apply_eq_iff_eq]`. Apply the tactic sequence `all_goals (try split_ifs)`. Apply the tactic sequence `all_goals (try simp_all)`.
-/
theorem Jd_submatrix (X : Data E r) : (Jd X).submatrix (eS X) (eS X) = -Jf (r - X.p0) X.p0 := by
  ext a b
  rcases a with i | j <;> rcases b with k | l <;>
    simp [Jd, Jf, Matrix.diagonal_apply, Matrix.one_apply, sgn, eS_inl, eS_inr, Equiv.apply_eq_iff_eq]
  all_goals (try split_ifs)
  all_goals (try simp_all)

/- English proof (translation)
Establish `hgram : ∀ (y : Frame X.Ψ r) (σ : X.Ψ), gram σ.1 X.Gm (mat y σ) = (mat y σ)ᵀ * X.Gm.map σ.1 * (mat y σ).map (starRingEnd ℂ)`. Introduce `y σ`. Use extensionality with `a b`. Simplify using `only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Establish `hdet : ∀ y : Frame X.Ψ r, IsOrth X y → ∀ σ : X.Ψ, IsUnit (mat y σ).det`. Introduce `y hy σ`. Establish `h` using `congrArg Matrix.det (hy σ)`. Rewrite `h` using `[hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]`. Rewrite using `[isUnit_iff_ne_zero]`.

Introduce `h0`. Rewrite `h` using `[h0, zero_mul, zero_mul]`. Use `(Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm` and prove the remaining obligations. Simplify using `only [sgn]`. Apply the tactic sequence `split_ifs <;> norm_num`.

Unfold `gM`. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet x0 hx0 τ), Matrix.one_mul]`.
-/
theorem gM_mul (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat x0 τ * gM X x0 x τ = mat x τ := by
  have hgram : ∀ (y : Frame X.Ψ r) (σ : X.Ψ), gram σ.1 X.Gm (mat y σ) =
      (mat y σ)ᵀ * X.Gm.map σ.1 * (mat y σ).map (starRingEnd ℂ) := by
    intro y σ
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdet : ∀ y : Frame X.Ψ r, IsOrth X y → ∀ σ : X.Ψ, IsUnit (mat y σ).det := by
    intro y hy σ
    have h := congrArg Matrix.det (hy σ)
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, zero_mul, zero_mul] at h
    refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
    simp only [sgn]
    split_ifs <;> norm_num
  unfold gM
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet x0 hx0 τ), Matrix.one_mul]

/- English proof (translation)
Establish `hgram : ∀ (y : Frame X.Ψ r) (σ : X.Ψ), gram σ.1 X.Gm (mat y σ) = (mat y σ)ᵀ * X.Gm.map σ.1 * (mat y σ).map (starRingEnd ℂ)`. Introduce `y σ`. Use extensionality with `a b`. Simplify using `only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Establish `hdet : ∀ y : Frame X.Ψ r, IsOrth X y → ∀ σ : X.Ψ, IsUnit (mat y σ).det`. Introduce `y hy σ`. Establish `h` using `congrArg Matrix.det (hy σ)`. Rewrite `h` using `[hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]`. Rewrite using `[isUnit_iff_ne_zero]`.

Introduce `h0`. Rewrite `h` using `[h0, zero_mul, zero_mul]`. Use `(Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm` and prove the remaining obligations. Simplify using `only [sgn]`. Apply the tactic sequence `split_ifs <;> norm_num`.

Establish `hmul : mat x τ = mat x0 τ * gM X x0 x τ`. Unfold `gM`. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet x0 hx0 τ), Matrix.one_mul]`. Establish `h1` using `hx τ`. Rewrite `h1` using `[hgram, hmul, Matrix.transpose_mul, Matrix.map_mul]`.

Establish `h0` using `hx0 τ`. Rewrite `h0` using `[hgram]`. Use `conv_lhs => rw [show Jd X = (mat x0 τ)ᵀ * X.Gm.map τ.1 * (mat x0 τ).map (starRingEnd ℂ) from h0.symm]`. Rewrite using `[show Jd X = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) from rfl, ← h1]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem gM_gram (X : Data E r) {x0 x : Frame X.Ψ r} (hx0 : IsOrth X x0) (hx : IsOrth X x) (τ : X.Ψ) :
    (gM X x0 x τ)ᵀ * Jd X * (gM X x0 x τ).map (starRingEnd ℂ) = Jd X := by
  have hgram : ∀ (y : Frame X.Ψ r) (σ : X.Ψ), gram σ.1 X.Gm (mat y σ) =
      (mat y σ)ᵀ * X.Gm.map σ.1 * (mat y σ).map (starRingEnd ℂ) := by
    intro y σ
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdet : ∀ y : Frame X.Ψ r, IsOrth X y → ∀ σ : X.Ψ, IsUnit (mat y σ).det := by
    intro y hy σ
    have h := congrArg Matrix.det (hy σ)
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, zero_mul, zero_mul] at h
    refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
    simp only [sgn]
    split_ifs <;> norm_num
  have hmul : mat x τ = mat x0 τ * gM X x0 x τ := by
    unfold gM
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet x0 hx0 τ), Matrix.one_mul]
  have h1 := hx τ
  rw [hgram, hmul, Matrix.transpose_mul, Matrix.map_mul] at h1
  have h0 := hx0 τ
  rw [hgram] at h0
  conv_lhs => rw [show Jd X = (mat x0 τ)ᵀ * X.Gm.map τ.1 * (mat x0 τ).map (starRingEnd ℂ) from h0.symm]
  rw [show Jd X = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) from rfl, ← h1]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Establish `hg` using `gM_gram X hx0 hx τ`. Establish `hJ` using `Jd_submatrix X`. Unfold `IsUpq Mq`. Establish `hJf : Jf (r - X.p0) X.p0 = -(Jd X).submatrix (eS X) (eS X)` using `by rw [hJ, neg_neg]`. Rewrite using `[hJf]`.

Establish `hct : (((gM X x0 x τ).map (starRingEnd ℂ)).submatrix (eS X) (eS X))ᴴ = ((gM X x0 x τ)ᵀ).submatrix (eS X) (eS X)`. Use extensionality with `a b`. Simplify using `[Matrix.conjTranspose_apply, Matrix.transpose_apply]`. Rewrite using `[hct, Matrix.mul_neg, Matrix.neg_mul, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg]`.
-/
theorem Mq_isUpq (X : Data E r) {x0 x : Frame X.Ψ r} (hx0 : IsOrth X x0) (hx : IsOrth X x) (τ : X.Ψ) :
    IsUpq (Mq X x0 x τ) := by
  have hg := gM_gram X hx0 hx τ
  have hJ := Jd_submatrix X
  unfold IsUpq Mq
  have hJf : Jf (r - X.p0) X.p0 = -(Jd X).submatrix (eS X) (eS X) := by rw [hJ, neg_neg]
  rw [hJf]
  have hct : (((gM X x0 x τ).map (starRingEnd ℂ)).submatrix (eS X) (eS X))ᴴ =
      ((gM X x0 x τ)ᵀ).submatrix (eS X) (eS X) := by
    ext a b
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  rw [hct, Matrix.mul_neg, Matrix.neg_mul, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg]

/- English proof (translation)
Unfold `lminor`. Rewrite using `[RingHom.map_det]`. Use `congr 1`.
-/
theorem det_lowerBlock_eq_conj_minor (X : Data E r) (x0 x : Frame X.Ψ r) (τ : X.Ψ) :
    (Mq X x0 x τ).toBlocks₂₂.det =
      starRingEnd ℂ (lminor (gM X x0 x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩) := by
  unfold lminor
  rw [RingHom.map_det]
  congr 1

/- English proof (translation)
Unfold `lminor`. Use `set e := Fin.castLE (Nat.le_of_lt_succ i.isLt) with he`. Establish `hsub : (A * N).submatrix e e = A.submatrix e e * N.submatrix e e`. Use extensionality with `a c`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`.

Use `(Fintype.sum_of_injective e (Fin.castLE_injective _) _ _ (fun k hk => ?_) (fun k => rfl)).symm` and prove the remaining obligations. Establish `hk' : (i : ℕ) ≤ k`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hk ⟨⟨k, h⟩, Fin.ext rfl⟩`.

Apply `mul_eq_zero_of_right` to reduce the goal to its premises. Apply `hN` to reduce the goal to its premises. Use `show e c < k`. Rewrite using `[Fin.lt_iff_val_lt_val, he, Fin.coe_castLE]`. Use linear arithmetic over natural numbers and integers.

Establish `hT : (N.submatrix e e).BlockTriangular id`. Introduce `a c hac`. Apply `hN` to reduce the goal to its premises. Use `show e c < e a`. Rewrite using `[Fin.lt_iff_val_lt_val, he, Fin.coe_castLE, Fin.coe_castLE]`.

Conclude with `hac`. Rewrite using `[hsub, Matrix.det_mul, Matrix.det_of_upperTriangular hT]`. Both sides reduce to the same expression.
-/
theorem lminor_mul_upper {n : ℕ} (A N : Matrix (Fin n) (Fin n) ℂ) (hN : N.BlockTriangular id)
    (i : Fin (n + 1)) :
    lminor (A * N) i = lminor A i * ∏ j : Fin i,
      N (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
  unfold lminor
  set e := Fin.castLE (Nat.le_of_lt_succ i.isLt) with he
  have hsub : (A * N).submatrix e e = A.submatrix e e * N.submatrix e e := by
    ext a c
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    refine (Fintype.sum_of_injective e (Fin.castLE_injective _) _ _ (fun k hk => ?_) (fun k => rfl)).symm
    have hk' : (i : ℕ) ≤ k := by
      by_contra h
      push_neg at h
      exact hk ⟨⟨k, h⟩, Fin.ext rfl⟩
    apply mul_eq_zero_of_right
    apply hN
    show e c < k
    rw [Fin.lt_iff_val_lt_val, he, Fin.coe_castLE]
    omega
  have hT : (N.submatrix e e).BlockTriangular id := by
    intro a c hac
    apply hN
    show e c < e a
    rw [Fin.lt_iff_val_lt_val, he, Fin.coe_castLE, Fin.coe_castLE]
    exact hac
  rw [hsub, Matrix.det_mul, Matrix.det_of_upperTriangular hT]
  rfl

/- English proof (translation)
Unfold `lminor`. Rewrite using `[Matrix.det_of_lowerTriangular]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Simplify using `[mat, nmat]`. Introduce `a c hac`.

Establish `hlt : a < c` using `OrderDual.toDual_lt_toDual.1 hac`. Establish `hlt' : (a : ℕ) < c` using `hlt`. Establish `h1 : ¬ (Fin.castLE (Nat.le_of_lt_succ i.isLt) c < Fin.castLE (Nat.le_of_lt_succ i.isLt) a)`. Rewrite using `[Fin.lt_iff_val_lt_val, Fin.coe_castLE, Fin.coe_castLE]`. Use linear arithmetic over natural numbers and integers.

Establish `h2 : Fin.castLE (Nat.le_of_lt_succ i.isLt) a ≠ Fin.castLE (Nat.le_of_lt_succ i.isLt) c`. Introduce `h`. Establish `h3` using `congrArg Fin.val h`. Rewrite `h3` using `[Fin.coe_castLE, Fin.coe_castLE]`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [Matrix.submatrix_apply, mat, Matrix.of_apply, nmat, dif_neg h1, if_neg h2]`.
-/
theorem lminor_nmat (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (i : Fin (r + 1)) :
    lminor (mat (nmat X z) τ) i = 1 := by
  unfold lminor
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [mat, nmat]
  · intro a c hac
    have hlt : a < c := OrderDual.toDual_lt_toDual.1 hac
    have hlt' : (a : ℕ) < c := hlt
    have h1 : ¬ (Fin.castLE (Nat.le_of_lt_succ i.isLt) c < Fin.castLE (Nat.le_of_lt_succ i.isLt) a) := by
      rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE, Fin.coe_castLE]
      omega
    have h2 : Fin.castLE (Nat.le_of_lt_succ i.isLt) a ≠ Fin.castLE (Nat.le_of_lt_succ i.isLt) c := by
      intro h
      have h3 := congrArg Fin.val h
      rw [Fin.coe_castLE, Fin.coe_castLE] at h3
      omega
    simp only [Matrix.submatrix_apply, mat, Matrix.of_apply, nmat, dif_neg h1, if_neg h2]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def i0 (X : Data E r) : Fin (r + 1) := ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩

def rhY (X : Data E r) (x0 y : Frame X.Ψ r) : ℝ :=
  -∑ τ, (Real.log ‖dmin X.Gm y τ (i0 X)‖ - 2 * Real.log ‖lminor (gM X x0 y τ) (i0 X)‖)

def kaY (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (y : Frame X.Ψ r) : ℝ := Real.exp (-bb * rhY X x0 y)

/- English proof (translation)
Establish `hgram : ∀ (y : Frame X.Ψ r) (σ : X.Ψ), gram σ.1 X.Gm (mat y σ) = (mat y σ)ᵀ * X.Gm.map σ.1 * (mat y σ).map (starRingEnd ℂ)`. Introduce `y σ`. Use extensionality with `a b`. Simplify using `only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Establish `hdet : ∀ y : Frame X.Ψ r, IsOrth X y → ∀ σ : X.Ψ, IsUnit (mat y σ).det`. Introduce `y hy σ`. Establish `h` using `congrArg Matrix.det (hy σ)`. Rewrite `h` using `[hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]`. Rewrite using `[isUnit_iff_ne_zero]`.

Introduce `h0`. Rewrite `h` using `[h0, zero_mul, zero_mul]`. Use `(Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm` and prove the remaining obligations. Simplify using `only [sgn]`. Apply the tactic sequence `split_ifs <;> norm_num`.

Establish `hgM : ∀ σ : X.Ψ, gM X x0 (cpt X x0 z) σ = mat (nmat X z) σ`. Introduce `σ`. Use `show (mat x0 σ)⁻¹ * (mat x0 σ * mat (nmat X z) σ) = _`. Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hdet x0 hx0 σ), Matrix.one_mul]`. Unfold `rhY ReciprocityTheory.ChartRestriction.G.AR.Up.rhF`.

Simplify using `only [hgM, lminor_nmat, norm_one, Real.log_one, mul_zero, sub_zero]`. Both sides reduce to the same expression.
-/
theorem rhY_cpt (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) (z : V (nd X)) :
    rhY X x0 (cpt X x0 z) = rhF X x0 z := by
  have hgram : ∀ (y : Frame X.Ψ r) (σ : X.Ψ), gram σ.1 X.Gm (mat y σ) =
      (mat y σ)ᵀ * X.Gm.map σ.1 * (mat y σ).map (starRingEnd ℂ) := by
    intro y σ
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdet : ∀ y : Frame X.Ψ r, IsOrth X y → ∀ σ : X.Ψ, IsUnit (mat y σ).det := by
    intro y hy σ
    have h := congrArg Matrix.det (hy σ)
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, zero_mul, zero_mul] at h
    refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
    simp only [sgn]
    split_ifs <;> norm_num
  have hgM : ∀ σ : X.Ψ, gM X x0 (cpt X x0 z) σ = mat (nmat X z) σ := by
    intro σ
    show (mat x0 σ)⁻¹ * (mat x0 σ * mat (nmat X z) σ) = _
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hdet x0 hx0 σ), Matrix.one_mul]
  unfold rhY ReciprocityTheory.ChartRestriction.G.AR.Up.rhF
  simp only [hgM, lminor_nmat, norm_one, Real.log_one, mul_zero, sub_zero]
  rfl

/- English proof (translation)
Unfold `kaY ReciprocityTheory.ChartRestriction.G.AR.Up.kaF`. Rewrite using `[rhY_cpt X hx0 z]`.
-/
theorem kaY_cpt (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) (bb : ℝ) (z : V (nd X)) :
    kaY X x0 bb (cpt X x0 z) = kaF X x0 bb z := by
  unfold kaY ReciprocityTheory.ChartRestriction.G.AR.Up.kaF
  rw [rhY_cpt X hx0 z]

/- English proof (translation)
The claim follows from `Real.exp_pos _`.
-/
theorem kaY_pos (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (y : Frame X.Ψ r) : 0 < kaY X x0 bb y := Real.exp_pos _

/- English proof (translation)
Rewrite using `[det_lowerBlock_eq_conj_minor, Complex.normSq_conj, Complex.normSq_eq_norm_sq]`. Both sides reduce to the same expression.
-/
theorem normSq_Mq (X : Data E r) (x0 x : Frame X.Ψ r) (τ : X.Ψ) :
    Complex.normSq (Mq X x0 x τ).toBlocks₂₂.det = ‖lminor (gM X x0 x τ) (i0 X)‖ ^ 2 := by
  rw [det_lowerBlock_eq_conj_minor, Complex.normSq_conj, Complex.normSq_eq_norm_sq]
  rfl

/- English proof (translation)
Establish `hU` using `Mq_isUpq X hx0 hx τ`. Establish `hd` using `det_lowerBlock_eq_conj_minor X x0 x τ`. Introduce `h0`. Establish `hdet0 : (Mq X x0 x τ).toBlocks₂₂.det = 0`. Rewrite using `[hd]`.

Conclude with `(map_eq_zero _).2 h0`. Unfold `IsUpq at hU`. Establish `h22` using `congrArg Matrix.toBlocks₂₂ hU`. Rewrite `h22` using `[← Matrix.fromBlocks_toBlocks (Mq X x0 x τ)]`. Simplify using `only [Jf, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, add_zero, zero_add] at h22`.

Use `set B := (Mq X x0 x τ).toBlocks₁₂`. Use `set D := (Mq X x0 x τ).toBlocks₂₂`. Establish `hDD : Dᴴ * D = 1 + Bᴴ * B`. Establish `h2 : Bᴴ * B - Dᴴ * D = -1`. Rewrite using `[sub_eq_add_neg]`.

Simplify `h22` using `[Matrix.neg_mul]`. Establish `h3` using `congrArg (fun M => Bᴴ * B - M) h2`. Simplify using `only [sub_sub_cancel, sub_neg_eq_add] at h3`. Rewrite using `[h3, add_comm]`. Establish `hne : (1 + Bᴴ * B).det ≠ 0` using `by open scoped ComplexOrder in`.

Conclude with `(Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self B)).det_pos.ne'`. Rewrite `hne` using `[← hDD, Matrix.det_mul, hdet0, mul_zero]`. Conclude with `hne rfl`.
-/
theorem lminor_orth_ne (X : Data E r) {x0 x : Frame X.Ψ r} (hx0 : IsOrth X x0) (hx : IsOrth X x)
    (τ : X.Ψ) : lminor (gM X x0 x τ) (i0 X) ≠ 0 := by
  have hU := Mq_isUpq X hx0 hx τ
  have hd := det_lowerBlock_eq_conj_minor X x0 x τ
  intro h0
  have hdet0 : (Mq X x0 x τ).toBlocks₂₂.det = 0 := by
    rw [hd]
    exact (map_eq_zero _).2 h0
  unfold IsUpq at hU
  have h22 := congrArg Matrix.toBlocks₂₂ hU
  rw [← Matrix.fromBlocks_toBlocks (Mq X x0 x τ)] at h22
  simp only [Jf, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂,
    Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, add_zero, zero_add] at h22
  set B := (Mq X x0 x τ).toBlocks₁₂
  set D := (Mq X x0 x τ).toBlocks₂₂
  have hDD : Dᴴ * D = 1 + Bᴴ * B := by
    have h2 : Bᴴ * B - Dᴴ * D = -1 := by
      rw [sub_eq_add_neg]
      simpa [Matrix.neg_mul] using h22
    have h3 := congrArg (fun M => Bᴴ * B - M) h2
    simp only [sub_sub_cancel, sub_neg_eq_add] at h3
    rw [h3, add_comm]
  have hne : (1 + Bᴴ * B).det ≠ 0 := by
    open scoped ComplexOrder in
    exact (Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self B)).det_pos.ne'
  rw [← hDD, Matrix.det_mul, hdet0, mul_zero] at hne
  exact hne rfl

/- English proof (translation)
Unfold `gM`. Rewrite using `[show mat (rmul y b) τ = mat y τ * mat b τ from rfl, Matrix.mul_assoc]`.
-/
theorem gM_rmul (X : Data E r) (x0 y b : Frame X.Ψ r) (τ : X.Ψ) :
    gM X x0 (rmul y b) τ = gM X x0 y τ * mat b τ := by
  unfold gM
  rw [show mat (rmul y b) τ = mat y τ * mat b τ from rfl, Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[gM_rmul]`. Conclude with `lminor_mul_upper _ _ (fun a c h => (hb τ).2 a c h) i`.
-/
theorem lminor_gM_rmul (X : Data E r) (x0 y : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (i : Fin (r + 1)) :
    lminor (gM X x0 (rmul y b) τ) i = lminor (gM X x0 y τ) i * ∏ j : Fin i,
      mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
  rw [gM_rmul]
  exact lminor_mul_upper _ _ (fun a c h => (hb τ).2 a c h) i

/- English proof (translation)
Establish `hT : (mat b τ).BlockTriangular id` using `fun a c h => (hb τ).2 a c h`. Establish `hd` using `(hb τ).1`. Rewrite `hd` using `[Matrix.det_of_upperTriangular hT]`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `j _`.

Conclude with `(Finset.prod_ne_zero_iff.mp hd) _ (Finset.mem_univ _)`.
-/
theorem prod_bdiag_ne (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) ≠ 0 := by
  have hT : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  have hd := (hb τ).1
  rw [Matrix.det_of_upperTriangular hT] at hd
  rw [Finset.prod_ne_zero_iff]
  intro j _
  exact (Finset.prod_ne_zero_iff.mp hd) _ (Finset.mem_univ _)

/- English proof (translation)
Establish `hb` using `FrameDegreeData.bOf_mem X hy`. Establish `ho : IsOrth X (rmul y (FrameDegreeData.bOf X y))` using `FrameDegreeData.ortho_bOf X hy`. Establish `h` using `lminor_orth_ne X hx0 ho τ`. Rewrite `h` using `[lminor_gM_rmul X x0 y hb]`. Conclude with `left_ne_zero_of_mul h`.
-/
theorem lminor_gM_ne (X : Data E r) {x0 y : Frame X.Ψ r} (hx0 : IsOrth X x0) (hy : y ∈ X.dom)
    (τ : X.Ψ) : lminor (gM X x0 y τ) (i0 X) ≠ 0 := by
  have hb := FrameDegreeData.bOf_mem X hy
  have ho : IsOrth X (rmul y (FrameDegreeData.bOf X y)) := FrameDegreeData.ortho_bOf X hy
  have h := lminor_orth_ne X hx0 ho τ
  rw [lminor_gM_rmul X x0 y hb] at h
  exact left_ne_zero_of_mul h

/- English proof (translation)
Introduce `h`. Establish `h2` using `(hy τ).2 i`. Rewrite `h2` using `[h, Complex.zero_re, mul_zero]`. Conclude with `lt_irrefl _ h2`.
-/
theorem dmin_ne (X : Data E r) {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm y τ i ≠ 0 := by
  intro h
  have h2 := (hy τ).2 i
  rw [h, Complex.zero_re, mul_zero] at h2
  exact lt_irrefl _ h2

/- English proof (translation)
Establish `hgram : ∀ (y : Frame X.Ψ r) (σ : X.Ψ), gram σ.1 X.Gm (mat y σ) = (mat y σ)ᵀ * X.Gm.map σ.1 * (mat y σ).map (starRingEnd ℂ)`. Introduce `y σ`. Use extensionality with `a b`. Simplify using `only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Establish `hdet : ∀ y : Frame X.Ψ r, IsOrth X y → ∀ σ : X.Ψ, IsUnit (mat y σ).det`. Introduce `y hy σ`. Establish `h` using `congrArg Matrix.det (hy σ)`. Rewrite `h` using `[hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]`. Rewrite using `[isUnit_iff_ne_zero]`.

Introduce `h0`. Rewrite `h` using `[h0, zero_mul, zero_mul]`. Use `(Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm` and prove the remaining obligations. Simplify using `only [sgn]`. Apply the tactic sequence `split_ifs <;> norm_num`.

Establish `hlt : ∀ (N : Matrix (Fin r) (Fin r) ℂ) (i : Fin (r + 1)), lminor Nᵀ i = lminor N i`. Introduce `N i`. Unfold `lminor`. Rewrite using `[← Matrix.transpose_submatrix, Matrix.det_transpose]`. Establish `hdm : ∀ σ : X.Ψ, dmin X.Gm (rmul y b) σ (i0 X) = dmin X.Gm y σ (i0 X) * (∏ j : Fin (i0 X), mat b σ (Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) j) (Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) j)) * starRingEnd ℂ (∏ j : Fin (i0 X), mat b σ (Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) …`.

Introduce `σ`. Unfold `dmin`. Establish `e : gram σ.1 X.Gm (mat (rmul y b) σ) = (mat b σ)ᵀ * gram σ.1 X.Gm (mat y σ) * (mat b σ).map (starRingEnd ℂ)`. Rewrite using `[hgram, hgram, show mat (rmul y b) σ = mat y σ * mat b σ from rfl, Matrix.transpose_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Establish `hTb : ((mat b σ).map (starRingEnd ℂ)).BlockTriangular id` using `fun a c h => by`. Simplify using `[Matrix.map_apply, mat, Matrix.of_apply, (hb σ).2 a c h]`. Establish `hTb' : (mat b σ).BlockTriangular id` using `fun a c h => (hb σ).2 a c h`. Establish `hL : lminor ((mat b σ)ᵀ * gram σ.1 X.Gm (mat y σ)) (i0 X) = lminor (gram σ.1 X.Gm (mat y σ)) (i0 X) * ∏ j : Fin (i0 X), mat b σ (Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) j) (Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) j)`. Rewrite using `[← hlt, Matrix.transpose_mul, Matrix.transpose_transpose, lminor_mul_upper _ _ hTb', hlt]`.

Rewrite using `[e, lminor_mul_upper _ _ hTb, hL, map_prod]`. Simplify using `only [Matrix.map_apply]`. Unfold `rhY`. Use `congr 1`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[hdm σ, lminor_gM_rmul X x0 y hb σ (i0 X)]`. Establish `hP` using `prod_bdiag_ne X hb σ (i0 X)`. Establish `hd` using `dmin_ne X hy σ (i0 X)`. Establish `hl` using `lminor_gM_ne X hx0 hy σ`. Rewrite using `[norm_mul, norm_mul, norm_mul, RCLike.norm_conj, Real.log_mul (by positivity) (norm_ne_zero_iff.2 hP), Real.log_mul (norm_ne_zero_iff.2 hd) (norm_ne_zero_iff.2 hP), Real.log_mul (norm_ne_zero_iff.2 hl) (norm_ne_zero_iff.2 hP)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem rhY_rmul (X : Data E r) {x0 y : Frame X.Ψ r} (hx0 : IsOrth X x0) (hy : y ∈ X.dom)
    {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : rhY X x0 (rmul y b) = rhY X x0 y := by
  have hgram : ∀ (y : Frame X.Ψ r) (σ : X.Ψ), gram σ.1 X.Gm (mat y σ) =
      (mat y σ)ᵀ * X.Gm.map σ.1 * (mat y σ).map (starRingEnd ℂ) := by
    intro y σ
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdet : ∀ y : Frame X.Ψ r, IsOrth X y → ∀ σ : X.Ψ, IsUnit (mat y σ).det := by
    intro y hy σ
    have h := congrArg Matrix.det (hy σ)
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, zero_mul, zero_mul] at h
    refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
    simp only [sgn]
    split_ifs <;> norm_num
  have hlt : ∀ (N : Matrix (Fin r) (Fin r) ℂ) (i : Fin (r + 1)), lminor Nᵀ i = lminor N i := by
    intro N i
    unfold lminor
    rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
  have hdm : ∀ σ : X.Ψ, dmin X.Gm (rmul y b) σ (i0 X) = dmin X.Gm y σ (i0 X) *
      (∏ j : Fin (i0 X), mat b σ (Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) j)
        (Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) j)) *
      starRingEnd ℂ (∏ j : Fin (i0 X), mat b σ (Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) j)
        (Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) j)) := by
    intro σ
    unfold dmin
    have e : gram σ.1 X.Gm (mat (rmul y b) σ) =
        (mat b σ)ᵀ * gram σ.1 X.Gm (mat y σ) * (mat b σ).map (starRingEnd ℂ) := by
      rw [hgram, hgram, show mat (rmul y b) σ = mat y σ * mat b σ from rfl, Matrix.transpose_mul,
        Matrix.map_mul]
      simp only [Matrix.mul_assoc]
    have hTb : ((mat b σ).map (starRingEnd ℂ)).BlockTriangular id := fun a c h => by
      simp [Matrix.map_apply, mat, Matrix.of_apply, (hb σ).2 a c h]
    have hTb' : (mat b σ).BlockTriangular id := fun a c h => (hb σ).2 a c h
    have hL : lminor ((mat b σ)ᵀ * gram σ.1 X.Gm (mat y σ)) (i0 X) =
        lminor (gram σ.1 X.Gm (mat y σ)) (i0 X) *
          ∏ j : Fin (i0 X), mat b σ (Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) j)
            (Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) j) := by
      rw [← hlt, Matrix.transpose_mul, Matrix.transpose_transpose, lminor_mul_upper _ _ hTb', hlt]
    rw [e, lminor_mul_upper _ _ hTb, hL, map_prod]
    simp only [Matrix.map_apply]
  unfold rhY
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hdm σ, lminor_gM_rmul X x0 y hb σ (i0 X)]
  have hP := prod_bdiag_ne X hb σ (i0 X)
  have hd := dmin_ne X hy σ (i0 X)
  have hl := lminor_gM_ne X hx0 hy σ
  rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj,
    Real.log_mul (by positivity) (norm_ne_zero_iff.2 hP),
    Real.log_mul (norm_ne_zero_iff.2 hd) (norm_ne_zero_iff.2 hP),
    Real.log_mul (norm_ne_zero_iff.2 hl) (norm_ne_zero_iff.2 hP)]
  ring

/- English proof (translation)
Unfold `kaY`. Rewrite using `[rhY_rmul X hx0 hy hb]`.
-/
theorem kaY_rmul (X : Data E r) {x0 y : Frame X.Ψ r} (hx0 : IsOrth X x0) (hy : y ∈ X.dom)
    {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (bb : ℝ) : kaY X x0 bb (rmul y b) = kaY X x0 bb y := by
  unfold kaY
  rw [rhY_rmul X hx0 hy hb]

/- English proof (translation)
Establish `hdmin : ∀ σ : X.Ψ, dmin X.Gm x σ (i0 X) = 1`. Introduce `σ`. Unfold `dmin lminor`. Rewrite using `[hx σ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations.

Establish `ha : ((Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) a : Fin r) : ℕ) < X.p0`. Rewrite using `[Fin.coe_castLE]`. Conclude with `a.2`. Simplify using `only [Function.comp_apply, sgn, if_pos ha]`. Evaluate the numerical expressions.

Establish `hpos : ∀ σ : X.Ψ, 0 < ‖lminor (gM X x0 x σ) (i0 X)‖` using `fun σ => norm_pos_iff.2 (lminor_orth_ne X hx0 hx σ)`. Unfold `kaY rhY`. Simplify using `only [hdmin, norm_one, Real.log_one, zero_sub, Finset.sum_neg_distrib, neg_neg]`. Rewrite using `[Finset.mul_sum, Real.exp_sum]`. Use `Finset.prod_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Establish `ht` using `hpos σ`. Rewrite using `[normSq_Mq, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), Real.rpow_def_of_pos (by positivity), Real.log_pow]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kaY_orth (X : Data E r) {x0 x : Frame X.Ψ r} (hx0 : IsOrth X x0) (hx : IsOrth X x) (s : ℝ) :
    kaY X x0 s x = ∏ τ, (Complex.normSq (Mq X x0 x τ).toBlocks₂₂.det)⁻¹ ^ s := by
  have hdmin : ∀ σ : X.Ψ, dmin X.Gm x σ (i0 X) = 1 := by
    intro σ
    unfold dmin lminor
    rw [hx σ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    refine Finset.prod_eq_one fun a _ => ?_
    have ha : ((Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) a : Fin r) : ℕ) < X.p0 := by
      rw [Fin.coe_castLE]
      exact a.2
    simp only [Function.comp_apply, sgn, if_pos ha]
    norm_num
  have hpos : ∀ σ : X.Ψ, 0 < ‖lminor (gM X x0 x σ) (i0 X)‖ :=
    fun σ => norm_pos_iff.2 (lminor_orth_ne X hx0 hx σ)
  unfold kaY rhY
  simp only [hdmin, norm_one, Real.log_one, zero_sub, Finset.sum_neg_distrib, neg_neg]
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun σ _ => ?_
  have ht := hpos σ
  rw [normSq_Mq, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
    Real.rpow_def_of_pos (by positivity), Real.log_pow]
  congr 1
  push_cast
  ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Establish `hgram : ∀ (y : Frame X.Ψ r) (σ : X.Ψ), gram σ.1 X.Gm (mat y σ) = (mat y σ)ᵀ * X.Gm.map σ.1 * (mat y σ).map (starRingEnd ℂ)`. Introduce `y σ`. Use extensionality with `a b`. Simplify using `only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Establish `hdet : ∀ y : Frame X.Ψ r, IsOrth X y → ∀ σ : X.Ψ, IsUnit (mat y σ).det`. Introduce `y hy σ`. Establish `h` using `congrArg Matrix.det (hy σ)`. Rewrite `h` using `[hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]`. Rewrite using `[isUnit_iff_ne_zero]`.

Introduce `h0`. Rewrite `h` using `[h0, zero_mul, zero_mul]`. Use `(Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm` and prove the remaining obligations. Simplify using `only [sgn]`. Apply the tactic sequence `split_ifs <;> norm_num`.

Introduce `τ`. Use `⟨isUnit_iff_ne_zero.1 (hdet x hx τ), fun i => ?_⟩` and prove the remaining obligations. Establish `hd : dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ)`. Unfold `dmin lminor`. Rewrite using `[hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, psgn, Complex.ofReal_prod, Finset.prod_range]`.

Simplify using `[Fin.coe_castLE]`. Rewrite using `[hd, Complex.ofReal_re]`. Establish `hne : psgn X.p0 i ≠ 0`. Unfold `psgn`. Use `Finset.prod_ne_zero_iff.2 fun a _ => ?_` and prove the remaining obligations.

Unfold `sgn`. Apply the tactic sequence `split_ifs <;> norm_num`. Conclude with `mul_self_pos.2 hne`.
-/
theorem orth_mem_dom (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) : x ∈ X.dom := by
  have hgram : ∀ (y : Frame X.Ψ r) (σ : X.Ψ), gram σ.1 X.Gm (mat y σ) =
      (mat y σ)ᵀ * X.Gm.map σ.1 * (mat y σ).map (starRingEnd ℂ) := by
    intro y σ
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdet : ∀ y : Frame X.Ψ r, IsOrth X y → ∀ σ : X.Ψ, IsUnit (mat y σ).det := by
    intro y hy σ
    have h := congrArg Matrix.det (hy σ)
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, zero_mul, zero_mul] at h
    refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
    simp only [sgn]
    split_ifs <;> norm_num
  intro τ
  refine ⟨isUnit_iff_ne_zero.1 (hdet x hx τ), fun i => ?_⟩
  have hd : dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, psgn,
      Complex.ofReal_prod, Finset.prod_range]
    simp [Fin.coe_castLE]
  rw [hd, Complex.ofReal_re]
  have hne : psgn X.p0 i ≠ 0 := by
    unfold psgn
    refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
    unfold sgn
    split_ifs <;> norm_num
  exact mul_self_pos.2 hne

/- English proof (translation)
Establish `hd` using `orth_mem_dom X hx0`. Take `⟨U, hU, U', hU', hfin⟩` from `hPD x0 hd x0 hd`. Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.1 hU'`. Establish `hne : ∀ δ ∈ X.Γ, δ ≠ 1 → 0 < dist (lact δ x0) x0`. Introduce `δ hδ h1`.

Use `dist_pos.2 fun h => h1 (X.Γ_free δ hδ x0 hd (idF X) (idF_mem X) ?_)` and prove the remaining obligations. Rewrite using `[rmul_idF]`. Conclude with `h`. Use `set T := hfin.toFinset.filter (· ≠ 1) with hTdef`. Choose the witnesses or unpack the hypotheses as in `⟨ε1, hε1, hT⟩ : ∃ ε1 > 0, ∀ δ ∈ T, ε1 ≤ dist (lact δ x0) x0 := by`.

Break down `T.eq_empty_or_nonempty with h | h` into its components or cases. Conclude with `⟨1, one_pos, by simp [h]⟩`. Take `⟨δ0, hδ0, hmin⟩` from `T.exists_min_image (fun δ => dist (lact δ x0) x0) h`. Establish `h0` using `Finset.mem_filter.1 hδ0`. Conclude with `⟨_, hne δ0 (hfin.mem_toFinset.1 h0.1).1 h0.2, hmin⟩`.

Use `set ε' := min ε ε1 with hε'`. Establish `hε'0 : 0 < ε'` using `lt_min hε hε1`. Establish `hall : ∀ δ ∈ X.Γ, δ ≠ 1 → ε' ≤ dist (lact δ x0) x0`. Introduce `δ hδ h1`. Distinguish the cases in `hS : δ ∈ T`.

Conclude with `(min_le_right _ _).trans (hT δ hS)`. Use `(min_le_left _ _).trans (not_lt.1 fun hlt => hS ?_)` and prove the remaining obligations. Use `Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨hδ, x0, mem_of_mem_nhds hU, lact δ x0, hball (Metric.mem_ball.2 hlt), idF X, idF_mem X, (rmul_idF X _).symm⟩, h1⟩` and prove the remaining obligations. Use `set K0 : ℝ := ∑ τ, ∑ a, ∑ k, ‖x0 τ a k‖ + 1 with hK0def`. Establish `hK0 : ∀ τ a k, ‖x0 τ a k‖ ≤ K0`.

Introduce `τ a k`. Establish `h1 : ‖x0 τ a k‖ ≤ ∑ k', ‖x0 τ a k'‖` using `Finset.single_le_sum (f := fun k' => ‖x0 τ a k'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)`. Establish `h2 : ∑ k', ‖x0 τ a k'‖ ≤ ∑ a', ∑ k', ‖x0 τ a' k'‖` using `Finset.single_le_sum (f := fun a' => ∑ k', ‖x0 τ a' k'‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)`. Establish `h3 : ∑ a', ∑ k', ‖x0 τ a' k'‖ ≤ ∑ τ', ∑ a', ∑ k', ‖x0 τ' a' k'‖` using `Finset.single_le_sum (f := fun τ' => ∑ a', ∑ k', ‖x0 τ' a' k'‖) (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hK0pos : 0 < K0`. Establish `: 0 ≤ ∑ τ, ∑ a, ∑ k, ‖x0 τ a k‖` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨ε' / ((r : ℝ) * K0 + 1), by positivity, fun δ hδ h1 => ?_⟩` and prove the remaining obligations. Establish `hdist` using `hall δ hδ h1`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hlt : dist (lact δ x0) x0 < ε'`. Use `(dist_pi_lt_iff hε'0).2 fun τ => (dist_pi_lt_iff hε'0).2 fun a => (dist_pi_lt_iff hε'0).2 fun b => ?_` and prove the remaining obligations. Rewrite using `[dist_eq_norm]`.

Establish `hm` using `congrFun (congrFun (gM_mul X hx0 (lact δ x0) τ) a) b`. Establish `he : lact δ x0 τ a b - x0 τ a b = ∑ k, x0 τ a k * (gM X x0 (lact δ x0) τ k b - (1 : Matrix (Fin r) (Fin r) ℂ) k b)`. Rewrite using `[show lact δ x0 τ a b = mat (lact δ x0) τ a b from rfl, ← hm, Matrix.mul_apply]`. Simplify using `only [mul_sub, Finset.sum_sub_distrib, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Both sides reduce to the same expression.

Rewrite using `[he]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hK0 τ a k) (hcon τ k b).le (norm_nonneg _) hK0pos.le`. Use `_ = ε' * ((r : ℝ) * K0 / ((r : ℝ) * K0 + 1)) := by`.

Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ < ε' := mul_lt_of_lt_one_right hε'0 ((div_lt_one (by positivity)).2 (lt_add_one _))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sep (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) (hPD : PropDisc X) :
    ∃ c > 0, ∀ δ ∈ X.Γ, δ ≠ 1 → ∃ τ a b,
      c ≤ ‖gM X x0 (lact δ x0) τ a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ := by
  classical
  have hd := orth_mem_dom X hx0
  obtain ⟨U, hU, U', hU', hfin⟩ := hPD x0 hd x0 hd
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU'
  have hne : ∀ δ ∈ X.Γ, δ ≠ 1 → 0 < dist (lact δ x0) x0 := by
    intro δ hδ h1
    refine dist_pos.2 fun h => h1 (X.Γ_free δ hδ x0 hd (idF X) (idF_mem X) ?_)
    rw [rmul_idF]; exact h
  set T := hfin.toFinset.filter (· ≠ 1) with hTdef
  obtain ⟨ε1, hε1, hT⟩ : ∃ ε1 > 0, ∀ δ ∈ T, ε1 ≤ dist (lact δ x0) x0 := by
    rcases T.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨δ0, hδ0, hmin⟩ := T.exists_min_image (fun δ => dist (lact δ x0) x0) h
      have h0 := Finset.mem_filter.1 hδ0
      exact ⟨_, hne δ0 (hfin.mem_toFinset.1 h0.1).1 h0.2, hmin⟩
  set ε' := min ε ε1 with hε'
  have hε'0 : 0 < ε' := lt_min hε hε1
  have hall : ∀ δ ∈ X.Γ, δ ≠ 1 → ε' ≤ dist (lact δ x0) x0 := by
    intro δ hδ h1
    by_cases hS : δ ∈ T
    · exact (min_le_right _ _).trans (hT δ hS)
    · refine (min_le_left _ _).trans (not_lt.1 fun hlt => hS ?_)
      refine Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨hδ, x0, mem_of_mem_nhds hU, lact δ x0,
        hball (Metric.mem_ball.2 hlt), idF X, idF_mem X, (rmul_idF X _).symm⟩, h1⟩
  set K0 : ℝ := ∑ τ, ∑ a, ∑ k, ‖x0 τ a k‖ + 1 with hK0def
  have hK0 : ∀ τ a k, ‖x0 τ a k‖ ≤ K0 := by
    intro τ a k
    have h1 : ‖x0 τ a k‖ ≤ ∑ k', ‖x0 τ a k'‖ :=
      Finset.single_le_sum (f := fun k' => ‖x0 τ a k'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    have h2 : ∑ k', ‖x0 τ a k'‖ ≤ ∑ a', ∑ k', ‖x0 τ a' k'‖ :=
      Finset.single_le_sum (f := fun a' => ∑ k', ‖x0 τ a' k'‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
    have h3 : ∑ a', ∑ k', ‖x0 τ a' k'‖ ≤ ∑ τ', ∑ a', ∑ k', ‖x0 τ' a' k'‖ :=
      Finset.single_le_sum (f := fun τ' => ∑ a', ∑ k', ‖x0 τ' a' k'‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ τ)
    linarith
  have hK0pos : 0 < K0 := by
    have : 0 ≤ ∑ τ, ∑ a, ∑ k, ‖x0 τ a k‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  refine ⟨ε' / ((r : ℝ) * K0 + 1), by positivity, fun δ hδ h1 => ?_⟩
  have hdist := hall δ hδ h1
  by_contra hcon
  push Not at hcon
  have hlt : dist (lact δ x0) x0 < ε' := by
    refine (dist_pi_lt_iff hε'0).2 fun τ => (dist_pi_lt_iff hε'0).2 fun a =>
      (dist_pi_lt_iff hε'0).2 fun b => ?_
    rw [dist_eq_norm]
    have hm := congrFun (congrFun (gM_mul X hx0 (lact δ x0) τ) a) b
    have he : lact δ x0 τ a b - x0 τ a b = ∑ k, x0 τ a k *
        (gM X x0 (lact δ x0) τ k b - (1 : Matrix (Fin r) (Fin r) ℂ) k b) := by
      rw [show lact δ x0 τ a b = mat (lact δ x0) τ a b from rfl, ← hm, Matrix.mul_apply]
      simp only [mul_sub, Finset.sum_sub_distrib, Matrix.one_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
    rw [he]
    calc ‖∑ k, x0 τ a k * (gM X x0 (lact δ x0) τ k b - (1 : Matrix (Fin r) (Fin r) ℂ) k b)‖
        ≤ ∑ k, ‖x0 τ a k * (gM X x0 (lact δ x0) τ k b - (1 : Matrix (Fin r) (Fin r) ℂ) k b)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _k : Fin r, K0 * (ε' / ((r : ℝ) * K0 + 1)) := Finset.sum_le_sum fun k _ => by
          rw [norm_mul]
          exact mul_le_mul (hK0 τ a k) (hcon τ k b).le (norm_nonneg _) hK0pos.le
      _ = ε' * ((r : ℝ) * K0 / ((r : ℝ) * K0 + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ < ε' := mul_lt_of_lt_one_right hε'0 ((div_lt_one (by positivity)).2 (lt_add_one _))
  linarith

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
