import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantOrthogonality
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemIffConjugateNotMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul

open NumberField Matrix Complex
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm omegaStd)

namespace GlobalTheory.ThFr

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {g : ℕ}

open Classical in

def borMat (b : Frame X.Ψ r) : Matrix (X.Ψ × Fin r) (X.Ψ × Fin r) ℂ :=
  Matrix.of fun p q => if q.1 = p.1 then
    (if (p.2 : ℕ) < X.p0 then (mat b p.1)ᵀ p.2 q.2 else (mat b p.1)⁻¹ p.2 q.2) else 0

/- English proof (translation)
Simplify using `[borMat, h, mat]`.
-/
theorem borMat_of_lt (b : Frame X.Ψ r) (τ : X.Ψ) {a : Fin r} (h : (a : ℕ) < X.p0) (c : Fin r) :
    borMat X b (τ, a) (τ, c) = b τ c a := by
  simp [borMat, h, mat]

/- English proof (translation)
Simplify using `[borMat, not_lt.2 h]`.
-/
theorem borMat_of_le (b : Frame X.Ψ r) (τ : X.Ψ) {a : Fin r} (h : X.p0 ≤ (a : ℕ)) (c : Fin r) :
    borMat X b (τ, a) (τ, c) = (mat b τ)⁻¹ a c := by
  simp [borMat, not_lt.2 h]

/- English proof (translation)
Simplify using `[borMat, h]`.
-/
theorem borMat_of_ne (b : Frame X.Ψ r) {p q : X.Ψ × Fin r} (h : q.1 ≠ p.1) :
    borMat X b p q = 0 := by
  simp [borMat, h]

variable {X}

/- English proof (translation)
Simplify using `only [borMat, of_apply, if_pos h, transpose_apply]`. Use `split_ifs`. Conclude with `PerMove.bor_tri hb _ hq`. Both sides reduce to the same expression.
-/
theorem borMat_eq_zero_of_lt {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) {p q : X.Ψ × Fin r}
    (h : (p.2 : ℕ) < X.p0) (hq : p.2 < q.2) : borMat X b p q = 0 := by
  simp only [borMat, of_apply, if_pos h, transpose_apply]
  split_ifs
  · exact PerMove.bor_tri hb _ hq
  · rfl

/- English proof (translation)
Simplify using `only [borMat, of_apply, if_neg (not_lt.2 h)]`. Use `split_ifs`. Conclude with `PerMove.bor_inv_tri hb _ hq`. Both sides reduce to the same expression.
-/
theorem borMat_eq_zero_of_le {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) {p q : X.Ψ × Fin r}
    (h : X.p0 ≤ (p.2 : ℕ)) (hq : q.2 < p.2) : borMat X b p q = 0 := by
  simp only [borMat, of_apply, if_neg (not_lt.2 h)]
  split_ifs
  · exact PerMove.bor_inv_tri hb _ hq
  · rfl

/- English proof (translation)
Simplify using `only [borMat, of_apply, if_true, rowFac]`. Use `split_ifs`. Both sides reduce to the same expression. Conclude with `PerMove.bor_inv_diag hb _ _`.
-/
theorem borMat_diag {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (p : X.Ψ × Fin r) :
    borMat X b p p = rowFac X (fun τ a => b τ a a) p := by
  simp only [borMat, of_apply, if_true, rowFac]
  split_ifs
  · rfl
  · exact PerMove.bor_inv_diag hb _ _

/- English proof (translation)
Set `w : Fin r → ℤ` to `fun a => if (a : ℕ) < X.p0 then -(a : ℕ) - 1 else (a : ℕ)`. Establish `hw : Function.Injective w`. Introduce `a c h`. Simplify using `only [w] at h`. Use `ext`.

Apply the tactic sequence `split_ifs at h <;> omega`. Rewrite using `[PerMove.det_of_triangular (fun k => toLex (Fintype.equivFin X.Ψ (idx k).1, w (idx k).2)) ?_ _ fun k l hkl => ?_]`. Rewrite using `[← idx.prod_comp]`. Conclude with `Finset.prod_congr rfl fun k _ => borMat_diag hb _`. Introduce `k l h`.

Establish `h'` using `toLex.injective h`. Rewrite `h'` using `[Prod.mk.injEq]`. Conclude with `idx.injective (Prod.ext ((Fintype.equivFin X.Ψ).injective h'.1) (hw h'.2))`. Rewrite using `[submatrix_apply]`. Distinguish the cases in `hτ : (idx l).1 = (idx k).1`.

Simplify using `only [hτ, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or, w] at hkl`. Break down `lt_or_ge ((idx k).2 : ℕ) X.p0 with hk | hk` into its components or cases. Use `borMat_eq_zero_of_lt hb hk ?_` and prove the remaining obligations. Rewrite using `[Fin.lt_def]`. Apply the tactic sequence `split_ifs at hkl <;> omega`.

Use `borMat_eq_zero_of_le hb hk ?_` and prove the remaining obligations. Rewrite using `[Fin.lt_def]`. Apply the tactic sequence `split_ifs at hkl <;> omega`. Conclude with `borMat_of_ne X b hτ`.
-/
theorem det_borMat {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (idx : Fin g ≃ X.Ψ × Fin r) :
    ((borMat X b).submatrix idx idx).det = ∏ p, rowFac X (fun τ a => b τ a a) p := by
  let w : Fin r → ℤ := fun a => if (a : ℕ) < X.p0 then -(a : ℕ) - 1 else (a : ℕ)
  have hw : Function.Injective w := by
    intro a c h
    simp only [w] at h
    ext
    split_ifs at h <;> omega
  rw [PerMove.det_of_triangular
    (fun k => toLex (Fintype.equivFin X.Ψ (idx k).1, w (idx k).2)) ?_ _ fun k l hkl => ?_]
  · rw [← idx.prod_comp]
    exact Finset.prod_congr rfl fun k _ => borMat_diag hb _
  · intro k l h
    have h' := toLex.injective h
    rw [Prod.mk.injEq] at h'
    exact idx.injective (Prod.ext ((Fintype.equivFin X.Ψ).injective h'.1) (hw h'.2))
  · rw [submatrix_apply]
    by_cases hτ : (idx l).1 = (idx k).1
    · simp only [hτ, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or, w] at hkl
      rcases lt_or_ge ((idx k).2 : ℕ) X.p0 with hk | hk
      · refine borMat_eq_zero_of_lt hb hk ?_
        rw [Fin.lt_def]
        split_ifs at hkl <;> omega
      · refine borMat_eq_zero_of_le hb hk ?_
        rw [Fin.lt_def]
        split_ifs at hkl <;> omega
    · exact borMat_of_ne X b hτ

/- English proof (translation)
Rewrite using `[det_borMat hb]`. Conclude with `Finset.prod_ne_zero_iff.2 fun p _ => rowFac_ne_zero (fun τ a => PerMove.bor_diag_ne hb τ a) p`.
-/
theorem det_borMat_ne_zero {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (idx : Fin g ≃ X.Ψ × Fin r) :
    ((borMat X b).submatrix idx idx).det ≠ 0 := by
  rw [det_borMat hb]
  exact Finset.prod_ne_zero_iff.2 fun p _ =>
    rowFac_ne_zero (fun τ a => PerMove.bor_diag_ne hb τ a) p

/- English proof (translation)
Use function extensionality and compare the values at `⟨τ, a⟩`. Establish `hm : mat (rmul x b) τ = mat x τ * mat b τ` using `rfl`. Rewrite using `[mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_eq_single τ]`. Break down `lt_or_ge (a : ℕ) X.p0 with ha | ha` into its components or cases. Rewrite using `[per_of_lt X _ _ _ ha, hm, PerMove.hermC_col_mul]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[borMat_of_lt X b τ ha]`. Break down `lt_or_ge (c : ℕ) X.p0 with hc | hc` into its components or cases. Rewrite using `[per_of_lt X _ _ _ hc]`. Both sides reduce to the same expression.

Rewrite using `[PerMove.bor_tri hb τ (show a < c by rw [Fin.lt_def]; omega), (hb τ).2 c a (by rw [Fin.lt_def]; omega), zero_mul, zero_mul]`. Rewrite using `[per_of_le X _ _ _ ha, hm, Matrix.mul_inv_rev, ← mulVec_mulVec, mulVec, dotProduct]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[borMat_of_le X b τ ha]`. Break down `lt_or_ge (c : ℕ) X.p0 with hc | hc` into its components or cases.

Rewrite using `[PerMove.bor_inv_tri hb τ (show c < a by rw [Fin.lt_def]; omega), zero_mul, zero_mul]`. Rewrite using `[per_of_le X _ _ _ hc]`. Introduce `σ _ hσ`. Conclude with `Finset.sum_eq_zero fun c _ => by rw [borMat_of_ne X b hσ, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem per_rmul (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (v : Fin r → E) :
    per X (rmul x b) v = borMat X b *ᵥ per X x v := by
  funext ⟨τ, a⟩
  have hm : mat (rmul x b) τ = mat x τ * mat b τ := rfl
  rw [mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · rcases lt_or_ge (a : ℕ) X.p0 with ha | ha
    · rw [per_of_lt X _ _ _ ha, hm, PerMove.hermC_col_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [borMat_of_lt X b τ ha]
      rcases lt_or_ge (c : ℕ) X.p0 with hc | hc
      · rw [per_of_lt X _ _ _ hc]; rfl
      · rw [PerMove.bor_tri hb τ (show a < c by rw [Fin.lt_def]; omega),
          (hb τ).2 c a (by rw [Fin.lt_def]; omega), zero_mul, zero_mul]
    · rw [per_of_le X _ _ _ ha, hm, Matrix.mul_inv_rev, ← mulVec_mulVec, mulVec, dotProduct]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [borMat_of_le X b τ ha]
      rcases lt_or_ge (c : ℕ) X.p0 with hc | hc
      · rw [PerMove.bor_inv_tri hb τ (show c < a by rw [Fin.lt_def]; omega), zero_mul, zero_mul]
      · rw [per_of_le X _ _ _ hc]
  · intro σ _ hσ
    exact Finset.sum_eq_zero fun c _ => by rw [borMat_of_ne X b hσ, zero_mul]
  · simp

/- English proof (translation)
Rewrite using `[per_rmul x hb, submatrix_mulVec_equiv]`. Use `congr 2`. Use function extensionality and compare the values at `p`. Simplify using the standard rewrite rules.
-/
theorem per_rmul_idx (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) (v : Fin r → E) :
    per X (rmul x b) v ∘ idx = (borMat X b).submatrix idx idx *ᵥ (per X x v ∘ idx) := by
  rw [per_rmul x hb, submatrix_mulVec_equiv]
  congr 2
  funext p; simp

/- English proof (translation)
Use function extensionality and compare the values at `p`. Establish `hm : mat (lact γ x) p.1 = (γ : Matrix (Fin r) (Fin r) E).map p.1.1 * mat x p.1` using `rfl`. Rewrite using `[per_apply, per_apply, PerMove.emb_mulVec, hm]`. Use `split_ifs`. Rewrite using `[PerMove.col_mul, PerMove.hermC_unitary _ _ _ hγ]`.

Establish `hu : IsUnit ((γ : Matrix (Fin r) (Fin r) E).map p.1.1).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map p.1.1.mapMatrix)`. Rewrite using `[Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]`.
-/
theorem per_lact (x : Frame X.Ψ r) {γ : GL (Fin r) E}
    (hγ : ∀ u v, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm X.Gm u v) (v : Fin r → E) :
    per X (lact γ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = per X x v := by
  funext p
  have hm : mat (lact γ x) p.1 = (γ : Matrix (Fin r) (Fin r) E).map p.1.1 * mat x p.1 := rfl
  rw [per_apply, per_apply, PerMove.emb_mulVec, hm]
  split_ifs
  · rw [PerMove.col_mul, PerMove.hermC_unitary _ _ _ hγ]
  · have hu : IsUnit ((γ : Matrix (Fin r) (Fin r) E).map p.1.1).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map p.1.1.mapMatrix)
    rw [Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]

variable (X) in

/- English proof (translation)
Establish `hent : ∀ τ a c, Differentiable ℂ fun x : Frame X.Ψ r => mat x τ a c`. Introduce `τ a c`. Use `show Differentiable ℂ fun x : Frame X.Ψ r => x τ a c`. Use `fun_prop`. Simplify using `only [per_apply]`.

Use `split_ifs`. Use `Differentiable.differentiableOn ?_` and prove the remaining obligations. Unfold `hermC FD.col`. Use `Differentiable.fun_sum fun a _ => Differentiable.fun_sum fun c _ => ?_` and prove the remaining obligations. Conclude with `((hent _ _ _).mul_const _).mul_const _`.

Simplify using `only [PerMove.inv_mulVec_apply]`. Use `DifferentiableOn.fun_mul (DifferentiableOn.fun_inv (PerMove.differentiable_det _ (hent _)).differentiableOn fun x hx => (hx _).1) (PerMove.differentiable_det _ fun a c => ?_).differentiableOn` and prove the remaining obligations. Simplify using `only [Matrix.updateCol_apply]`. Use `split_ifs`. Conclude with `differentiable_const _`.

Conclude with `hent _ _ _`.
-/
theorem differentiableOn_per (v : Fin r → E) (p : X.Ψ × Fin r) :
    DifferentiableOn ℂ (fun x => per X x v p) X.dom := by
  have hent : ∀ τ a c, Differentiable ℂ fun x : Frame X.Ψ r => mat x τ a c := by
    intro τ a c
    show Differentiable ℂ fun x : Frame X.Ψ r => x τ a c
    fun_prop
  simp only [per_apply]
  split_ifs
  · refine Differentiable.differentiableOn ?_
    unfold hermC FD.col
    refine Differentiable.fun_sum fun a _ => Differentiable.fun_sum fun c _ => ?_
    exact ((hent _ _ _).mul_const _).mul_const _
  · simp only [PerMove.inv_mulVec_apply]
    refine DifferentiableOn.fun_mul (DifferentiableOn.fun_inv
      (PerMove.differentiable_det _ (hent _)).differentiableOn fun x hx => (hx _).1)
      (PerMove.differentiable_det _ fun a c => ?_).differentiableOn
    simp only [Matrix.updateCol_apply]
    split_ifs
    · exact differentiable_const _
    · exact hent _ _ _

variable (X) in

def Hm (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) :
    Matrix (Fin g) (Fin g) ℂ :=
  (hMat X bas idx x)ᵀ * imInv X bas idx x * (hMat X bas idx x).map conj

variable (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

/- English proof (translation)
The claim follows from `(RiemannRel.hermForm_mulVec _ _ _ z w).symm`.
-/
theorem hermForm_Hm (x : Frame X.Ψ r) (z w : Fin g → ℂ) :
    hermForm (Hm X bas idx x) z w =
      hermForm (imInv X bas idx x) (hMat X bas idx x *ᵥ z) (hMat X bas idx x *ᵥ w) :=
  (RiemannRel.hermForm_mulVec _ _ _ z w).symm

section Rmul

variable (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
include hb

/- English proof (translation)
Use extensionality with `i k`. Conclude with `congrFun (per_rmul_idx idx x hb (bas (Pi.single (s k) 1))) i`.
-/
theorem perMat_rmul (s : Fin g → Fin g ⊕ Fin g) :
    perMat X bas idx s (rmul x b) = (borMat X b).submatrix idx idx * perMat X bas idx s x := by
  ext i k
  exact congrFun (per_rmul_idx idx x hb (bas (Pi.single (s k) 1))) i

/- English proof (translation)
Rewrite using `[hMat, perMat_rmul bas idx x hb, Matrix.mul_inv_rev, hMat]`.
-/
theorem hMat_rmul :
    hMat X bas idx (rmul x b) = hMat X bas idx x * ((borMat X b).submatrix idx idx)⁻¹ := by
  rw [hMat, perMat_rmul bas idx x hb, Matrix.mul_inv_rev, hMat]

/- English proof (translation)
Rewrite using `[hMat_rmul bas idx x hb, nonsing_inv_mul_cancel_right _ _ (det_borMat_ne_zero hb idx).isUnit]`.
-/
theorem hMat_rmul_mul :
    hMat X bas idx (rmul x b) * (borMat X b).submatrix idx idx = hMat X bas idx x := by
  rw [hMat_rmul bas idx x hb, nonsing_inv_mul_cancel_right _ _ (det_borMat_ne_zero hb idx).isUnit]

/- English proof (translation)
Rewrite using `[hMat_rmul bas idx x hb, det_mul, det_nonsing_inv, det_borMat hb, Ring.inverse_eq_inv', Finset.prod_inv_distrib]`.
-/
theorem det_hMat_rmul : (hMat X bas idx (rmul x b)).det =
    (hMat X bas idx x).det * ∏ p, (rowFac X (fun τ a => b τ a a) p)⁻¹ := by
  rw [hMat_rmul bas idx x hb, det_mul, det_nonsing_inv, det_borMat hb, Ring.inverse_eq_inv',
    Finset.prod_inv_distrib]

/- English proof (translation)
Rewrite using `[tauMat, perMat_rmul bas idx x hb, ← Matrix.mul_assoc, hMat_rmul_mul bas idx x hb, tauMat]`.
-/
theorem tauMat_rmul : tauMat X bas idx (rmul x b) = tauMat X bas idx x := by
  rw [tauMat, perMat_rmul bas idx x hb, ← Matrix.mul_assoc, hMat_rmul_mul bas idx x hb, tauMat]

/- English proof (translation)
Rewrite using `[imInv, tauMat_rmul bas idx x hb, imInv]`.
-/
theorem imInv_rmul : imInv X bas idx (rmul x b) = imInv X bas idx x := by
  rw [imInv, tauMat_rmul bas idx x hb, imInv]

/- English proof (translation)
Rewrite using `[hermForm_Hm, hermForm_Hm, mulVec_mulVec, mulVec_mulVec, hMat_rmul_mul bas idx x hb, imInv_rmul bas idx x hb]`.
-/
theorem hermForm_Hm_rmul (z w : Fin g → ℂ) :
    hermForm (Hm X bas idx (rmul x b)) ((borMat X b).submatrix idx idx *ᵥ z)
      ((borMat X b).submatrix idx idx *ᵥ w) = hermForm (Hm X bas idx x) z w := by
  rw [hermForm_Hm, hermForm_Hm, mulVec_mulVec, mulVec_mulVec, hMat_rmul_mul bas idx x hb,
    imInv_rmul bas idx x hb]

end Rmul

variable (X) in

/- English proof (translation)
The claim follows from `mul_pos two_pos (norm_pos_iff.2 ((map_ne_zero τ.1).2 X.ξ0_ne))`.
-/
theorem c_pos (τ : X.Ψ) : 0 < X.c τ :=
  mul_pos two_pos (norm_pos_iff.2 ((map_ne_zero τ.1).2 X.ξ0_ne))

variable (X) in

/- English proof (translation)
Establish `hξ : (τ.1 X.ξ0).re = 0`. Establish `h` using `congrArg Complex.re (PerMove.map_cc τ.1 X.ξ0)`. Rewrite `h` using `[X.ξ0_im, map_neg, neg_re, conj_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpos` using `im_neg_half_pos X τ`.

Establish `hn : |(τ.1 X.ξ0).im| = ‖τ.1 X.ξ0‖` using `Complex.abs_im_eq_norm.mpr hξ`. Establish `key : τ.1 (-(X.κ0 / 2)) = -τ.1 X.ξ0 ∨ τ.1 (-(X.κ0 / 2)) = τ.1 X.ξ0`. Break down `X.κ0_xi with h | h` into its components or cases. Use `left`. Rewrite using `[← map_neg, h]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `right`. Rewrite using `[h]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Apply `Complex.ext` to reduce the goal to its premises. Apply the tactic sequence `rcases key with h | h <;> simp [h, hξ]`. Simplify using `only [mul_im, I_re, I_im, ofReal_re, ofReal_im, mul_zero, one_mul, zero_add, Data.c, ← hn]`. Apply the tactic sequence `rcases key with h | h <;> rw [h] at hpos ⊢`.

Rewrite `hpos`, the goal using `[neg_im]`. Rewrite using `[abs_of_neg (by linarith)]; ring`. Rewrite using `[abs_of_pos hpos]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem emb_neg_half (τ : X.Ψ) : τ.1 (-(X.κ0 / 2)) = I * (X.c τ / 2 : ℝ) := by
  have hξ : (τ.1 X.ξ0).re = 0 := by
    have h := congrArg Complex.re (PerMove.map_cc τ.1 X.ξ0)
    rw [X.ξ0_im, map_neg, neg_re, conj_re] at h
    linarith
  have hpos := im_neg_half_pos X τ
  have hn : |(τ.1 X.ξ0).im| = ‖τ.1 X.ξ0‖ := Complex.abs_im_eq_norm.mpr hξ
  have key : τ.1 (-(X.κ0 / 2)) = -τ.1 X.ξ0 ∨ τ.1 (-(X.κ0 / 2)) = τ.1 X.ξ0 := by
    rcases X.κ0_xi with h | h
    · left; rw [← map_neg, h]; congr 1; ring
    · right; rw [h]; congr 1; ring
  apply Complex.ext
  · rcases key with h | h <;> simp [h, hξ]
  · simp only [mul_im, I_re, I_im, ofReal_re, ofReal_im, mul_zero, one_mul, zero_add, Data.c, ← hn]
    rcases key with h | h <;> rw [h] at hpos ⊢
    · rw [neg_im] at hpos ⊢
      rw [abs_of_neg (by linarith)]; ring
    · rw [abs_of_pos hpos]; ring

variable (X) in

/- English proof (translation)
Rewrite using `[EF_def, UnitFrame.trace_eq_sum_re X.Ψ X.cmType]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, emb_neg_half, ← hermC_emb]`. Simplify using `only [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem EF_eq_sum (u v : Fin r → E) : (EF X u v : ℝ) =
    ∑ τ : X.Ψ, X.c τ * -(hermC τ.1 X.Gm (Data.emb τ.1 u) (Data.emb τ.1 v)).im := by
  rw [EF_def, UnitFrame.trace_eq_sum_re X.Ψ X.cmType]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_mul, emb_neg_half, ← hermC_emb]
  simp only [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im]
  ring

/- English proof (translation)
Simplify using `only [Finset.mul_sum]`. Rewrite using `[← Fintype.sum_prod_type' (fun τ a => (X.c τ : ℂ) * (z (τ, a) * conj (w (τ, a)))), hermForm, dotProduct]`. Use `Fintype.sum_equiv idx _ _ fun k => ?_` and prove the remaining obligations. Rewrite using `[mulVec_diagonal]`. Simplify using `only [Function.comp_apply, Pi.star_apply, RCLike.star_def]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermForm_diagonal_c (z w : X.Ψ × Fin r → ℂ) :
    hermForm (Matrix.diagonal fun i => (X.c (idx i).1 : ℂ)) (z ∘ idx) (w ∘ idx) =
      ∑ τ, (X.c τ : ℂ) * ∑ a, z (τ, a) * conj (w (τ, a)) := by
  simp only [Finset.mul_sum]
  rw [← Fintype.sum_prod_type' (fun τ a => (X.c τ : ℂ) * (z (τ, a) * conj (w (τ, a)))), hermForm,
    dotProduct]
  refine Fintype.sum_equiv idx _ _ fun k => ?_
  rw [mulVec_diagonal]
  simp only [Function.comp_apply, Pi.star_apply, RCLike.star_def]
  ring

/- English proof (translation)
Rewrite using `[hermForm_diagonal_c, EF_eq_sum, im_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[im_ofReal_mul, ← UnitFrame.im_sum_periods X.p0 τ.1 X.Gm (mat x τ) (ho τ)]`. Both sides reduce to the same expression.
-/
theorem im_hermForm_diagonal_c {x : Frame X.Ψ r} (ho : X.IsOrtho x) (u v : Fin r → E) :
    (hermForm (Matrix.diagonal fun i => (X.c (idx i).1 : ℂ)) (per X x u ∘ idx)
      (per X x v ∘ idx)).im = EF X u v := by
  rw [hermForm_diagonal_c, EF_eq_sum, im_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [im_ofReal_mul, ← UnitFrame.im_sum_periods X.p0 τ.1 X.Gm (mat x τ) (ho τ)]
  rfl

/- English proof (translation)
Rewrite using `[per_apply]`. Use `split_ifs with ha`. Establish `hu : mat x p.1 *ᵥ ((mat x p.1)⁻¹ *ᵥ Data.emb p.1.1 v) = Data.emb p.1.1 v`. Rewrite using `[mulVec_mulVec, mul_nonsing_inv _ (hx p.1).1.isUnit, one_mulVec]`. Establish `hcol : FD.col (mat x p.1) p.2 = mat x p.1 *ᵥ Pi.single p.2 1`.

Use extensionality with `k`. Simplify using `[FD.col]`. Use `conv_lhs => rw [hcol, ← hu]`. Rewrite using `[UnitFrame.hermC_mulVec, ho]`. Simplify using `[mulVec_diagonal, sgn, ha]`.

Both sides reduce to the same expression.
-/
theorem norm_per_of_isOrtho {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (v : Fin r → E)
    (p : X.Ψ × Fin r) : ‖per X x v p‖ = ‖((mat x p.1)⁻¹ *ᵥ Data.emb p.1.1 v) p.2‖ := by
  rw [per_apply]
  split_ifs with ha
  · have hu : mat x p.1 *ᵥ ((mat x p.1)⁻¹ *ᵥ Data.emb p.1.1 v) = Data.emb p.1.1 v := by
      rw [mulVec_mulVec, mul_nonsing_inv _ (hx p.1).1.isUnit, one_mulVec]
    have hcol : FD.col (mat x p.1) p.2 = mat x p.1 *ᵥ Pi.single p.2 1 := by
      ext k; simp [FD.col]
    conv_lhs => rw [hcol, ← hu]
    rw [UnitFrame.hermC_mulVec, ho]
    simp [mulVec_diagonal, sgn, ha]
  · rfl

/- English proof (translation)
Rewrite using `[hermForm_diagonal_c]`. Use `push_cast`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[MajorantOrthogonality.maj_ortho X hx ho, ReciprocityTheory.MultiplicativeHeights.normSq]`. Use `push_cast`.

Use `congrArg _ (Finset.sum_congr rfl fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[mul_conj, normSq_eq_norm_sq, norm_per_of_isOrtho hx ho]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem hermForm_diagonal_c_self {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x)
    (v : Fin r → E) :
    hermForm (Matrix.diagonal fun i => (X.c (idx i).1 : ℂ)) (per X x v ∘ idx) (per X x v ∘ idx) =
      ((∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) : ℝ) : ℂ) := by
  rw [hermForm_diagonal_c]
  push_cast
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [MajorantOrthogonality.maj_ortho X hx ho, ReciprocityTheory.MultiplicativeHeights.normSq]
  push_cast
  refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [mul_conj, normSq_eq_norm_sq, norm_per_of_isOrtho hx ho]
  push_cast
  rfl

/- English proof (translation)
Rewrite `hN` using `[Matrix.map_mul, ← Matrix.mul_assoc]`. Generalize the expression as in `Aᵀ * G * A.map conj = M at hM hN`. Use extensionality with `j k`. Establish `h` using `hN j k`. Simplify using `only [mul_apply, im_sum, map_apply, mul_im, hM, conj_im, zero_mul, add_zero, mul_neg, Finset.sum_neg_distrib, neg_inj] at h`.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using `only [mul_apply, re_sum, map_apply, re_mul_ofReal, h]`. Apply the tactic sequence `by_cases hjk : j = k <;> simp [one_apply, hjk]`. Simplify using `only [mul_apply, im_sum, map_apply, im_mul_ofReal, hM]`. Apply the tactic sequence `by_cases hjk : j = k <;> simp [one_apply, hjk]`.
-/
theorem gram_mul_im (G A τ : Matrix (Fin g) (Fin g) ℂ)
    (hM : ∀ j k, ((Aᵀ * G * A.map conj) j k).im = 0)
    (hN : ∀ j k, ((Aᵀ * G * (A * τ).map conj) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k) :
    Aᵀ * G * A.map conj * τ.map (fun z => (z.im : ℂ)) = 1 := by
  rw [Matrix.map_mul, ← Matrix.mul_assoc] at hN
  generalize Aᵀ * G * A.map conj = M at hM hN
  ext j k
  have h := hN j k
  simp only [mul_apply, im_sum, map_apply, mul_im, hM, conj_im, zero_mul, add_zero, mul_neg,
    Finset.sum_neg_distrib, neg_inj] at h
  apply Complex.ext
  · simp only [mul_apply, re_sum, map_apply, re_mul_ofReal, h]
    by_cases hjk : j = k <;> simp [one_apply, hjk]
  · simp only [mul_apply, im_sum, map_apply, im_mul_ofReal, hM]
    by_cases hjk : j = k <;> simp [one_apply, hjk]

variable {bas}

/- English proof (translation)
Use `set G : Matrix (Fin g) (Fin g) ℂ := Matrix.diagonal fun i => (X.c (idx i).1 : ℂ) with hG`. Use `set A := perMat X bas idx Sum.inl x with hA`. Use `set B := perMat X bas idx Sum.inr x with hB`. Establish `hE (s t : Fin g → Fin g ⊕ Fin g) (j k : Fin g) : (((perMat X bas idx s x)ᵀ * G * (perMat X bas idx t x).map conj) j k).im = -(omegaStd (Pi.single (s j) 1) (Pi.single (t k) 1) : ℤ)`. Rewrite using `[← RiemannRel.hermForm_col, perMat_mulVec_single, perMat_mulVec_single, hG, im_hermForm_diagonal_c idx ho, hs]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hM : ∀ j k, ((Aᵀ * G * A.map conj) j k).im = 0` using `fun j k => by`. Rewrite using `[hE]`. Simplify using `[omegaStd]`.

Establish `hN : ∀ j k, ((Aᵀ * G * B.map conj) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k`. Introduce `j k`. Rewrite using `[hE]`. Distinguish the cases in `h : j = k`. Substitute `h` using the available equality.

Simplify using `[omegaStd, Pi.single_apply]`. Simplify using `[omegaStd, Pi.single_apply, h, Ne.symm h]`. Establish `hK : ∀ j k, ((Bᵀ * G * B.map conj) j k).im = 0` using `fun j k => by`. Rewrite using `[hE]`. Simplify using `[omegaStd]`.

Establish `hH : G.IsHermitian`. Rewrite using `[hG, Matrix.isHermitian_diagonal_iff]`. Introduce `a`. Conclude with `Complex.conj_ofReal _`. Establish `hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm G z z).re`.

Introduce `z hz`. Take `⟨k, hk⟩` from `Function.ne_iff.1 hz`. Establish `h : (hermForm G z z).re = ∑ i, X.c (idx i).1 * normSq (z i)`. Rewrite using `[hermForm, dotProduct, re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hG, mulVec_diagonal, mul_left_comm, Pi.star_apply, RCLike.star_def, mul_conj, ← ofReal_mul, ofReal_re]`. Rewrite using `[h]`. Conclude with `Finset.sum_pos' (fun i _ => mul_nonneg (c_pos X _).le (normSq_nonneg _)) ⟨k, Finset.mem_univ _, mul_pos (c_pos X _) (normSq_pos.2 hk)⟩`. Establish `hdet` using `RiemannRel.det_ne_zero G A B hpos hM hN`. Establish `hu : IsUnit A.det` using `hdet.isUnit`.

Establish `hAB : A * tauMat X bas idx x = B` using `mul_nonsing_inv_cancel_left _ _ hu`. Establish `h` using `RiemannRel.symm_posDef G A _ hH hdet hpos hM (by rw [hAB]; exact hN) (by rw [hAB]; exact hK)`. Use `⟨hu, h.1, h.2, ?_⟩` and prove the remaining obligations. Establish `h1 : A * hMat X bas idx x = 1` using `mul_nonsing_inv _ hu`. Rewrite using `[Hm, imInv_eq, inv_eq_left_inv (gram_mul_im G A _ hM (by rw [hAB]; exact hN))]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[transpose_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = G := by rw [h1]; simp`.
-/
theorem riemann_of_isOrtho (hs : IsSympl X bas) {x : Frame X.Ψ r} (ho : X.IsOrtho x) :
    IsUnit (perMat X bas idx Sum.inl x).det ∧ (tauMat X bas idx x).IsSymm ∧
      ((tauMat X bas idx x).map Complex.im).PosDef ∧
      Hm X bas idx x = Matrix.diagonal fun i => (X.c (idx i).1 : ℂ) := by
  set G : Matrix (Fin g) (Fin g) ℂ := Matrix.diagonal fun i => (X.c (idx i).1 : ℂ) with hG
  set A := perMat X bas idx Sum.inl x with hA
  set B := perMat X bas idx Sum.inr x with hB
  have hE (s t : Fin g → Fin g ⊕ Fin g) (j k : Fin g) :
      (((perMat X bas idx s x)ᵀ * G * (perMat X bas idx t x).map conj) j k).im =
        -(omegaStd (Pi.single (s j) 1) (Pi.single (t k) 1) : ℤ) := by
    rw [← RiemannRel.hermForm_col, perMat_mulVec_single, perMat_mulVec_single, hG,
      im_hermForm_diagonal_c idx ho, hs]
    push_cast
    rfl
  have hM : ∀ j k, ((Aᵀ * G * A.map conj) j k).im = 0 := fun j k => by
    rw [hE]; simp [omegaStd]
  have hN : ∀ j k, ((Aᵀ * G * B.map conj) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k := by
    intro j k
    rw [hE]
    by_cases h : j = k
    · subst h
      simp [omegaStd, Pi.single_apply]
    · simp [omegaStd, Pi.single_apply, h, Ne.symm h]
  have hK : ∀ j k, ((Bᵀ * G * B.map conj) j k).im = 0 := fun j k => by
    rw [hE]; simp [omegaStd]
  have hH : G.IsHermitian := by
    rw [hG, Matrix.isHermitian_diagonal_iff]
    intro a; exact Complex.conj_ofReal _
  have hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm G z z).re := by
    intro z hz
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hz
    have h : (hermForm G z z).re = ∑ i, X.c (idx i).1 * normSq (z i) := by
      rw [hermForm, dotProduct, re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hG, mulVec_diagonal, mul_left_comm, Pi.star_apply, RCLike.star_def, mul_conj,
        ← ofReal_mul, ofReal_re]
    rw [h]
    exact Finset.sum_pos' (fun i _ => mul_nonneg (c_pos X _).le (normSq_nonneg _))
      ⟨k, Finset.mem_univ _, mul_pos (c_pos X _) (normSq_pos.2 hk)⟩
  have hdet := RiemannRel.det_ne_zero G A B hpos hM hN
  have hu : IsUnit A.det := hdet.isUnit
  have hAB : A * tauMat X bas idx x = B := mul_nonsing_inv_cancel_left _ _ hu
  have h := RiemannRel.symm_posDef G A _ hH hdet hpos hM (by rw [hAB]; exact hN)
    (by rw [hAB]; exact hK)
  refine ⟨hu, h.1, h.2, ?_⟩
  have h1 : A * hMat X bas idx x = 1 := mul_nonsing_inv _ hu
  rw [Hm, imInv_eq, inv_eq_left_inv (gram_mul_im G A _ hM (by rw [hAB]; exact hN))]
  calc _ = (A * hMat X bas idx x)ᵀ * G * (A * hMat X bas idx x).map conj := by
        rw [transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
    _ = G := by rw [h1]; simp

/- English proof (translation)
The claim follows from `(riemann_of_isOrtho idx hs ho).2.2.2`.
-/
theorem Hm_of_isOrtho (hs : IsSympl X bas) {x : Frame X.Ψ r} (ho : X.IsOrtho x) :
    Hm X bas idx x = Matrix.diagonal fun i => (X.c (idx i).1 : ℂ) :=
  (riemann_of_isOrtho idx hs ho).2.2.2

/- English proof (translation)
Rewrite using `[Hm_of_isOrtho idx hs ho, det_diagonal, idx.prod_comp fun p => (X.c p.1 : ℂ), Fintype.prod_prod_type]`. Simplify using the standard rewrite rules.
-/
theorem det_Hm_of_isOrtho (hs : IsSympl X bas) {x : Frame X.Ψ r} (ho : X.IsOrtho x) :
    (Hm X bas idx x).det = ((∏ τ, X.c τ ^ r : ℝ) : ℂ) := by
  rw [Hm_of_isOrtho idx hs ho, det_diagonal, idx.prod_comp fun p => (X.c p.1 : ℂ),
    Fintype.prod_prod_type]
  simp

section Dom

variable (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
include hs hx

/- English proof (translation)
Establish `h` using `(riemann_of_isOrtho idx hs (FrameDegreeData.ortho_bOf X hx)).1`. Rewrite `h` using `[perMat_rmul bas idx x (FrameDegreeData.bOf_mem X hx), det_mul]`. Conclude with `isUnit_of_mul_isUnit_right h`.
-/
theorem isUnit_det_perMat : IsUnit (perMat X bas idx Sum.inl x).det := by
  have h := (riemann_of_isOrtho idx hs (FrameDegreeData.ortho_bOf X hx)).1
  rw [perMat_rmul bas idx x (FrameDegreeData.bOf_mem X hx), det_mul] at h
  exact isUnit_of_mul_isUnit_right h

/- English proof (translation)
The claim follows from `isUnit_nonsing_inv_det _ (isUnit_det_perMat idx hs hx)`.
-/
theorem isUnit_det_hMat : IsUnit (hMat X bas idx x).det :=
  isUnit_nonsing_inv_det _ (isUnit_det_perMat idx hs hx)

/- English proof (translation)
The claim follows from `nonsing_inv_mul _ (isUnit_det_perMat idx hs hx)`.
-/
theorem hMat_mul_perMat : hMat X bas idx x * perMat X bas idx Sum.inl x = 1 :=
  nonsing_inv_mul _ (isUnit_det_perMat idx hs hx)

/- English proof (translation)
The claim follows from `tauMat_rmul bas idx x (FrameDegreeData.bOf_mem X hx) ▸ (riemann_of_isOrtho idx hs (FrameDegreeData.ortho_bOf X hx)).2.1`.
-/
theorem tauMat_isSymm : (tauMat X bas idx x).IsSymm :=
  tauMat_rmul bas idx x (FrameDegreeData.bOf_mem X hx) ▸
    (riemann_of_isOrtho idx hs (FrameDegreeData.ortho_bOf X hx)).2.1

/- English proof (translation)
The claim follows from `tauMat_rmul bas idx x (FrameDegreeData.bOf_mem X hx) ▸ (riemann_of_isOrtho idx hs (FrameDegreeData.ortho_bOf X hx)).2.2.1`.
-/
theorem tauMat_im_posDef : ((tauMat X bas idx x).map Complex.im).PosDef :=
  tauMat_rmul bas idx x (FrameDegreeData.bOf_mem X hx) ▸
    (riemann_of_isOrtho idx hs (FrameDegreeData.ortho_bOf X hx)).2.2.1

/- English proof (translation)
The claim follows from `hMat_mulVec_per X bas idx (isUnit_det_perMat idx hs hx) _`.
-/
theorem hMat_mulVec_per_bas (m n : Fin g → ℤ) :
    hMat X bas idx x *ᵥ (per X x (bas (Sum.elim m n)) ∘ idx) =
      (fun k => (m k : ℂ)) + tauMat X bas idx x *ᵥ fun k => (n k : ℂ) :=
  hMat_mulVec_per X bas idx (isUnit_det_perMat idx hs hx) _

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Complex.ofRealHom.mapMatrix _ * Complex.ofRealHom.mapMatrix ((tauMat X bas idx x).map Complex.im) = 1`. Rewrite using `[← map_mul, nonsing_inv_mul _ (tauMat_im_posDef idx hs hx).det_pos.ne'.isUnit, map_one]`.
-/
theorem imInv_mul_im :
    imInv X bas idx x * (tauMat X bas idx x).map (fun z => (z.im : ℂ)) = 1 := by
  change Complex.ofRealHom.mapMatrix _ *
    Complex.ofRealHom.mapMatrix ((tauMat X bas idx x).map Complex.im) = 1
  rw [← map_mul, nonsing_inv_mul _ (tauMat_im_posDef idx hs hx).det_pos.ne'.isUnit, map_one]

/- English proof (translation)
Establish `h` using `(tauMat_im_posDef idx hs hx).inv.isHermitian`. Use extensionality with `i j`. Use `congrFun (congrFun h i) j` as an intermediate fact. Simplify using `only [conjTranspose_apply, star_trivial] at this`. Simplify using `[imInv, this]`.
-/
theorem imInv_isSymm : (imInv X bas idx x).IsSymm := by
  have h := (tauMat_im_posDef idx hs hx).inv.isHermitian
  ext i j
  have := congrFun (congrFun h i) j
  simp only [conjTranspose_apply, star_trivial] at this
  simp [imInv, this]

/- English proof (translation)
Establish `h : (imInv X bas idx x).IsHermitian`. Use extensionality with `i j`. Rewrite using `[conjTranspose_apply, (imInv_isSymm idx hs hx).apply]`. Conclude with `Complex.conj_ofReal _`. Conclude with `Matrix.isHermitian_mul_mul_conjTranspose (hMat X bas idx x)ᵀ h`.
-/
theorem Hm_isHermitian : (Hm X bas idx x).IsHermitian := by
  have h : (imInv X bas idx x).IsHermitian := by
    ext i j
    rw [conjTranspose_apply, (imInv_isSymm idx hs hx).apply]
    exact Complex.conj_ofReal _
  exact Matrix.isHermitian_mul_mul_conjTranspose (hMat X bas idx x)ᵀ h

/- English proof (translation)
Rewrite using `[← hermForm_Hm_rmul bas idx x (FrameDegreeData.bOf_mem X hx), Hm_of_isOrtho idx hs (FrameDegreeData.ortho_bOf X hx)]`.
-/
theorem hermForm_Hm_eq_diagonal (z w : Fin g → ℂ) :
    hermForm (Hm X bas idx x) z w = hermForm (Matrix.diagonal fun i => (X.c (idx i).1 : ℂ))
      ((borMat X (FrameDegreeData.bOf X x)).submatrix idx idx *ᵥ z)
      ((borMat X (FrameDegreeData.bOf X x)).submatrix idx idx *ᵥ w) := by
  rw [← hermForm_Hm_rmul bas idx x (FrameDegreeData.bOf_mem X hx),
    Hm_of_isOrtho idx hs (FrameDegreeData.ortho_bOf X hx)]

/- English proof (translation)
Rewrite using `[hermForm_Hm_eq_diagonal idx hs hx]`. Use `set y := (borMat X (FrameDegreeData.bOf X x)).submatrix idx idx *ᵥ z with hy`. Establish `hy0 : y ≠ 0` using `fun h => det_borMat_ne_zero (FrameDegreeData.bOf_mem X hx) idx (Matrix.exists_mulVec_eq_zero_iff.1 ⟨z, hz, h⟩)`. Take `⟨k, hk⟩` from `Function.ne_iff.1 hy0`. Establish `h : (hermForm (Matrix.diagonal fun i => (X.c (idx i).1 : ℂ)) y y).re = ∑ i, X.c (idx i).1 * normSq (y i)`.

Rewrite using `[hermForm, dotProduct, re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mulVec_diagonal, mul_left_comm, Pi.star_apply, RCLike.star_def, mul_conj, ← ofReal_mul, ofReal_re]`. Rewrite using `[h]`. Conclude with `Finset.sum_pos' (fun i _ => mul_nonneg (c_pos X _).le (normSq_nonneg _)) ⟨k, Finset.mem_univ _, mul_pos (c_pos X _) (normSq_pos.2 hk)⟩`.
-/
theorem hermForm_Hm_pos {z : Fin g → ℂ} (hz : z ≠ 0) : 0 < (hermForm (Hm X bas idx x) z z).re := by
  rw [hermForm_Hm_eq_diagonal idx hs hx]
  set y := (borMat X (FrameDegreeData.bOf X x)).submatrix idx idx *ᵥ z with hy
  have hy0 : y ≠ 0 := fun h => det_borMat_ne_zero (FrameDegreeData.bOf_mem X hx) idx
    (Matrix.exists_mulVec_eq_zero_iff.1 ⟨z, hz, h⟩)
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hy0
  have h : (hermForm (Matrix.diagonal fun i => (X.c (idx i).1 : ℂ)) y y).re =
      ∑ i, X.c (idx i).1 * normSq (y i) := by
    rw [hermForm, dotProduct, re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mulVec_diagonal, mul_left_comm, Pi.star_apply, RCLike.star_def, mul_conj,
      ← ofReal_mul, ofReal_re]
  rw [h]
  exact Finset.sum_pos' (fun i _ => mul_nonneg (c_pos X _).le (normSq_nonneg _))
    ⟨k, Finset.mem_univ _, mul_pos (c_pos X _) (normSq_pos.2 hk)⟩

/- English proof (translation)
Rewrite using `[hermForm_Hm_eq_diagonal idx hs hx, ← per_rmul_idx idx x (FrameDegreeData.bOf_mem X hx), ← per_rmul_idx idx x (FrameDegreeData.bOf_mem X hx), im_hermForm_diagonal_c idx (FrameDegreeData.ortho_bOf X hx)]`.
-/
theorem im_hermForm_Hm (u v : Fin r → E) :
    (hermForm (Hm X bas idx x) (per X x u ∘ idx) (per X x v ∘ idx)).im = EF X u v := by
  rw [hermForm_Hm_eq_diagonal idx hs hx, ← per_rmul_idx idx x (FrameDegreeData.bOf_mem X hx),
    ← per_rmul_idx idx x (FrameDegreeData.bOf_mem X hx), im_hermForm_diagonal_c idx (FrameDegreeData.ortho_bOf X hx)]

/- English proof (translation)
Establish `h1` using `congrArg det (imInv_mul_im idx hs hx)`. Establish `h2 : ((tauMat X bas idx x).map (fun z => (z.im : ℂ))).det = (((tauMat X bas idx x).map Complex.im).det : ℂ)` using `(Complex.ofRealHom.map_det _).symm`. Establish `h3 : ((hMat X bas idx x).map conj).det = conj (hMat X bas idx x).det` using `((starRingEnd ℂ).map_det _).symm`. Rewrite `h1` using `[det_mul, h2, det_one]`. Rewrite using `[Hm, det_mul, det_mul, det_transpose, h3, ← normSq_eq_norm_sq, ← mul_conj]`.

Take the linear combination `(hMat X bas idx x).det * conj (hMat X bas idx x).det * h1`.
-/
theorem det_im_mul_det_Hm :
    (((tauMat X bas idx x).map Complex.im).det : ℂ) * (Hm X bas idx x).det =
      ((‖(hMat X bas idx x).det‖ ^ 2 : ℝ) : ℂ) := by
  have h1 := congrArg det (imInv_mul_im idx hs hx)
  have h2 : ((tauMat X bas idx x).map (fun z => (z.im : ℂ))).det =
      (((tauMat X bas idx x).map Complex.im).det : ℂ) :=
    (Complex.ofRealHom.map_det _).symm
  have h3 : ((hMat X bas idx x).map conj).det = conj (hMat X bas idx x).det :=
    ((starRingEnd ℂ).map_det _).symm
  rw [det_mul, h2, det_one] at h1
  rw [Hm, det_mul, det_mul, det_transpose, h3, ← normSq_eq_norm_sq, ← mul_conj]
  linear_combination (hMat X bas idx x).det * conj (hMat X bas idx x).det * h1

/- English proof (translation)
Establish `h` using `ofReal_ne_zero.2 (tauMat_im_posDef idx hs hx).det_pos.ne'`. Rewrite using `[ofReal_div, eq_div_iff h, mul_comm, det_im_mul_det_Hm idx hs hx]`.
-/
theorem det_Hm : (Hm X bas idx x).det =
    ((‖(hMat X bas idx x).det‖ ^ 2 / ((tauMat X bas idx x).map Complex.im).det : ℝ) : ℂ) := by
  have h := ofReal_ne_zero.2 (tauMat_im_posDef idx hs hx).det_pos.ne'
  rw [ofReal_div, eq_div_iff h, mul_comm, det_im_mul_det_Hm idx hs hx]

/- English proof (translation)
Rewrite using `[det_Hm idx hs hx, ofReal_re]`. Conclude with `div_pos (pow_pos (norm_pos_iff.2 (isUnit_det_hMat idx hs hx).ne_zero) 2) (tauMat_im_posDef idx hs hx).det_pos`.
-/
theorem det_Hm_re_pos : 0 < (Hm X bas idx x).det.re := by
  rw [det_Hm idx hs hx, ofReal_re]
  exact div_pos (pow_pos (norm_pos_iff.2 (isUnit_det_hMat idx hs hx).ne_zero) 2)
    (tauMat_im_posDef idx hs hx).det_pos

/- English proof (translation)
Rewrite using `[eq_div_iff (det_Hm_re_pos idx hs hx).ne', ← re_ofReal_mul, det_im_mul_det_Hm idx hs hx, ofReal_re]`.
-/
theorem det_im_tauMat : ((tauMat X bas idx x).map Complex.im).det =
    ‖(hMat X bas idx x).det‖ ^ 2 / (Hm X bas idx x).det.re := by
  rw [eq_div_iff (det_Hm_re_pos idx hs hx).ne', ← re_ofReal_mul, det_im_mul_det_Hm idx hs hx,
    ofReal_re]

end Dom

/- English proof (translation)
The claim follows from `RiemannRel.differentiableOn_left_inverse (perMat X bas idx Sum.inl) _ (fun _ _ => differentiableOn_per X _ _) (fun _ hx => hMat_mul_perMat idx hs hx) i j`.
-/
theorem differentiableOn_hMat (hs : IsSympl X bas) (i j : Fin g) :
    DifferentiableOn ℂ (fun x => hMat X bas idx x i j) X.dom :=
  RiemannRel.differentiableOn_left_inverse (perMat X bas idx Sum.inl) _
    (fun _ _ => differentiableOn_per X _ _) (fun _ hx => hMat_mul_perMat idx hs hx) i j

/- English proof (translation)
The claim follows from `RiemannRel.differentiableOn_det _ (differentiableOn_hMat idx hs)`.
-/
theorem differentiableOn_det_hMat (hs : IsSympl X bas) :
    DifferentiableOn ℂ (fun x => (hMat X bas idx x).det) X.dom :=
  RiemannRel.differentiableOn_det _ (differentiableOn_hMat idx hs)

/- English proof (translation)
Simplify using `only [tauMat, mul_apply]`. Conclude with `DifferentiableOn.fun_sum fun l _ => (differentiableOn_hMat idx hs i l).mul (differentiableOn_per X _ _)`.
-/
theorem differentiableOn_tauMat (hs : IsSympl X bas) (i j : Fin g) :
    DifferentiableOn ℂ (fun x => tauMat X bas idx x i j) X.dom := by
  simp only [tauMat, mul_apply]
  exact DifferentiableOn.fun_sum fun l _ =>
    (differentiableOn_hMat idx hs i l).mul (differentiableOn_per X _ _)

/- English proof (translation)
The claim follows from `tauMat_isSymm _ Gauss.isSympl_bas Gauss.one_mem`.
-/
example : (tauMat HyperbolicCusp.flagData Gauss.bas Gauss.idx Gauss.one).IsSymm :=
  tauMat_isSymm _ Gauss.isSympl_bas Gauss.one_mem

end

end GlobalTheory.ThFr
