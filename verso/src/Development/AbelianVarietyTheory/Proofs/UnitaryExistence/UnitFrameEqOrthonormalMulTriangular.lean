import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.UnitFrames

open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

section Mat

variable {n : ℕ}

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => left`. Simplify using `[psgn]`. Consider the case `succ k ih`. Rewrite using `[psgn_succ]`.

Apply the tactic sequence `rcases ih with h | h <;> rcases sgn_sq p0 k with h' | h' <;> simp [h, h']`.
-/
theorem psgn_sq (p0 k : ℕ) : psgn p0 k = 1 ∨ psgn p0 k = -1 := by
  induction k with
  | zero => left; simp [psgn]
  | succ k ih =>
    rw [psgn_succ]
    rcases ih with h | h <;> rcases sgn_sq p0 k with h' | h' <;> simp [h, h']

/- English proof (translation)
Rewrite using `[lminor_diagonal, psgn, Complex.ofReal_prod, Finset.prod_range]`. Both sides reduce to the same expression.
-/
theorem lminor_signature (p0 : ℕ) (i : Fin (n + 1)) :
    lminor (Matrix.diagonal fun a : Fin n => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) i
      = ((psgn p0 i : ℝ) : ℂ) := by
  rw [lminor_diagonal, psgn, Complex.ofReal_prod, Finset.prod_range]
  rfl

/- English proof (translation)
Establish `hdet : ∀ c : Fin n, (blk A c).det ≠ 0`. Introduce `c h0`. Establish `h` using `h1 ⟨c, Nat.lt_succ_of_lt c.isLt⟩`. Establish `: lminor A ⟨c, Nat.lt_succ_of_lt c.isLt⟩ = 0` using `h0`. Rewrite `h` using `[this]`.

Simplify using `at h`. Use `set B := (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ) with hB`. Establish `hH : B.IsHermitian`. Establish `e : (uMat A).map (starRingEnd ℂ) = ((uMat A)ᵀ)ᴴ`. Use extensionality with `a c`.

Simplify using `[Matrix.conjTranspose_apply]`. Rewrite using `[hB, e]`. Conclude with `Matrix.isHermitian_mul_mul_conjTranspose _ hA`. Establish `hdiag : B = Matrix.diagonal fun k => B k k`. Use extensionality with `a c`.

Break down `lt_trichotomy a c with hac | hac | hac` into its components or cases. Rewrite using `[Matrix.diagonal_apply_ne _ (ne_of_lt hac), ← hH.apply a c, hB, uGu_lower _ hdet hac, star_zero]`. Substitute `hac` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq]`. Rewrite using `[Matrix.diagonal_apply_ne _ (ne_of_gt hac), hB, uGu_lower _ hdet hac]`.

Establish `hprod : ∀ i : Fin (n + 1), lminor A i = ∏ j : Fin i, (fun k => B k k) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)`. Introduce `i`. Establish `e : lminor B i = lminor A i`. Rewrite using `[hB, lminor_conj (uMat_upper _) i]`. Simplify using `only [uMat_diag, Finset.prod_const_one, one_mul, map_one, mul_one]`.

Rewrite using `[← e]`. Conclude with `(congrArg (fun M => lminor M i) hdiag).trans (lminor_diagonal _ i)`. Establish `hre : ∀ k, (B k k).im = 0` using `fun k => Complex.conj_eq_iff_im.1 (hH.apply k k)`. Establish `hval : ∀ i : Fin (n + 1), lminor A i = ((psgn p0 i : ℝ) : ℂ)`. Introduce `i`.

Establish `him : (lminor A i).im = 0`. Rewrite using `[hprod i]`. Use `Complex.conj_eq_iff_im.1 ?_` and prove the remaining obligations. Rewrite using `[map_prod]`. Conclude with `Finset.prod_congr rfl fun j _ => Complex.conj_eq_iff_im.2 (hre _)`.

Apply the tactic sequence `have hd : lminor A i = (((lminor A i).re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]`. Establish `hn` using `h1 i`. Establish `hp` using `hs i`. Rewrite `hn` using `[hd, Complex.norm_real, Real.norm_eq_abs]`. Rewrite using `[hd, Complex.ofReal_inj]`.

Apply the tactic sequence `rcases psgn_sq p0 i with h | h <;> rw [h] at hp ⊢`. Rewrite using `[abs_of_pos (by linarith)] at hn; exact hn`. Rewrite using `[abs_of_neg (by linarith)] at hn; linarith`. Rewrite using `[hdiag]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Establish `hsucc : lminor A k.succ = lminor A k.castSucc * B k k`. Rewrite using `[hprod k.succ, hprod k.castSucc]`. Conclude with `prod_castLE_succ (f := fun k => B k k) k.isLt`. Rewrite `hsucc` using `[hval, hval, Fin.val_succ, Fin.val_castSucc, psgn_succ, Complex.ofReal_mul]`.

Establish `hne : ((psgn p0 k : ℝ) : ℂ) ≠ 0`. Apply the tactic sequence `rcases psgn_sq p0 k with h | h <;> simp [h]`. Conclude with `(mul_left_cancel₀ hne hsucc).symm`.
-/
theorem uMat_conj_eq_signature (p0 : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hs : ∀ i : Fin (n + 1), 0 < psgn p0 i * (lminor A i).re)
    (h1 : ∀ i : Fin (n + 1), ‖lminor A i‖ = 1) :
    (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ)
      = Matrix.diagonal fun a : Fin n => ((sgn p0 (a : ℕ) : ℝ) : ℂ) := by
  have hdet : ∀ c : Fin n, (blk A c).det ≠ 0 := by
    intro c h0
    have h := h1 ⟨c, Nat.lt_succ_of_lt c.isLt⟩
    have : lminor A ⟨c, Nat.lt_succ_of_lt c.isLt⟩ = 0 := h0
    rw [this] at h
    simp at h
  set B := (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ) with hB
  have hH : B.IsHermitian := by
    have e : (uMat A).map (starRingEnd ℂ) = ((uMat A)ᵀ)ᴴ := by
      ext a c; simp [Matrix.conjTranspose_apply]
    rw [hB, e]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hA
  have hdiag : B = Matrix.diagonal fun k => B k k := by
    ext a c
    rcases lt_trichotomy a c with hac | hac | hac
    · rw [Matrix.diagonal_apply_ne _ (ne_of_lt hac), ← hH.apply a c, hB,
        uGu_lower _ hdet hac, star_zero]
    · subst hac
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ (ne_of_gt hac), hB, uGu_lower _ hdet hac]
  have hprod : ∀ i : Fin (n + 1), lminor A i
      = ∏ j : Fin i, (fun k => B k k) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
    intro i
    have e : lminor B i = lminor A i := by
      rw [hB, lminor_conj (uMat_upper _) i]
      simp only [uMat_diag, Finset.prod_const_one, one_mul, map_one, mul_one]
    rw [← e]
    exact (congrArg (fun M => lminor M i) hdiag).trans (lminor_diagonal _ i)
  have hre : ∀ k, (B k k).im = 0 := fun k => Complex.conj_eq_iff_im.1 (hH.apply k k)
  have hval : ∀ i : Fin (n + 1), lminor A i = ((psgn p0 i : ℝ) : ℂ) := by
    intro i
    have him : (lminor A i).im = 0 := by
      rw [hprod i]
      refine Complex.conj_eq_iff_im.1 ?_
      rw [map_prod]
      exact Finset.prod_congr rfl fun j _ => Complex.conj_eq_iff_im.2 (hre _)
    have hd : lminor A i = (((lminor A i).re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
    have hn := h1 i
    have hp := hs i
    rw [hd, Complex.norm_real, Real.norm_eq_abs] at hn
    rw [hd, Complex.ofReal_inj]
    rcases psgn_sq p0 i with h | h <;> rw [h] at hp ⊢
    · rw [abs_of_pos (by linarith)] at hn; exact hn
    · rw [abs_of_neg (by linarith)] at hn; linarith
  rw [hdiag]
  congr 1
  funext k
  have hsucc : lminor A k.succ = lminor A k.castSucc * B k k := by
    rw [hprod k.succ, hprod k.castSucc]
    exact prod_castLE_succ (f := fun k => B k k) k.isLt
  rw [hval, hval, Fin.val_succ, Fin.val_castSucc, psgn_succ, Complex.ofReal_mul] at hsucc
  have hne : ((psgn p0 k : ℝ) : ℂ) ≠ 0 := by
    rcases psgn_sq p0 k with h | h <;> simp [h]
  exact (mul_left_cancel₀ hne hsucc).symm

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular (uMat_upper _)]`. Simplify using `only [uMat_diag, Finset.prod_const_one]`.
-/
theorem det_uMat (A : Matrix (Fin n) (Fin n) ℂ) : (uMat A).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (uMat_upper _)]
  simp only [uMat_diag, Finset.prod_const_one]

/- English proof (translation)
Use `haveI := Matrix.invertibleOfIsUnitDet (uMat A) (by rw [det_uMat]; exact isUnit_one)`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular (uMat_upper A)`.
-/
theorem inv_uMat_upper (A : Matrix (Fin n) (Fin n) ℂ) : (uMat A)⁻¹.BlockTriangular id := by
  haveI := Matrix.invertibleOfIsUnitDet (uMat A) (by rw [det_uMat]; exact isUnit_one)
  exact Matrix.blockTriangular_inv_of_blockTriangular (uMat_upper A)

/- English proof (translation)
Establish `h` using `congrFun (congrFun (Matrix.nonsing_inv_mul (uMat A) (by rw [det_uMat]; exact isUnit_one)) i) i`. Rewrite `h` using `[Matrix.mul_apply, Finset.sum_eq_single i, uMat_diag, mul_one, Matrix.one_apply_eq]`. Conclude with `h`. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h' | h'` into its components or cases.

Rewrite using `[inv_uMat_upper A h', zero_mul]`. Rewrite using `[uMat_upper A h', mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem inv_uMat_diag (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : (uMat A)⁻¹ i i = 1 := by
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul (uMat A)
    (by rw [det_uMat]; exact isUnit_one)) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, uMat_diag, mul_one, Matrix.one_apply_eq] at h
  · exact h
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h' | h'
    · rw [inv_uMat_upper A h', zero_mul]
    · rw [uMat_upper A h', mul_zero]
  · simp

end Mat

/- English proof (translation)
Introduce `E _ _ _ r p0 Ψ Gm hG`. Use `⟨fun x hx h1 => ?_, fun x₀ h => ⟨fun τ => ⟨?_, fun i => ?_⟩, fun τ i => ?_⟩, fun τ u x₀ hu => ?_⟩` and prove the remaining obligations. Use `⟨fun τ => (mat x τ * uMat (gram τ.1 Gm (mat x τ)) : Matrix _ _ ℂ), fun τ => ((uMat (gram τ.1 Gm (mat x τ)))⁻¹ : Matrix _ _ ℂ), fun τ => ⟨?_, fun a c hca => ?_⟩, fun τ => ?_, fun τ i => ?_, ?_⟩` and prove the remaining obligations. Use `show ((uMat (gram τ.1 Gm (mat x τ)))⁻¹).det ≠ 0`. Rewrite using `[Matrix.det_nonsing_inv, det_uMat]`.

Simplify using the standard rewrite rules. Conclude with `inv_uMat_upper _ hca`. Use `show gram τ.1 Gm (mat x τ * uMat (gram τ.1 Gm (mat x τ))) = _`. Rewrite using `[FrameDegreeData.gram_mul]`. Conclude with `uMat_conj_eq_signature p0 _ (gram_isHermitian τ.1 hG _) (hx τ).2 (h1 τ)`.

Use `show ‖(uMat (gram τ.1 Gm (mat x τ)))⁻¹ i i‖ = 1`. Rewrite using `[inv_uMat_diag, norm_one]`. Use function extensionality and compare the values at `τ show mat x τ = (mat x τ * uMat (gram τ.1 Gm (mat x τ))) * (uMat (gram τ.1 Gm (mat x τ)))⁻¹`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_right _ _ (by rw [det_uMat]; exact isUnit_one)]`. Introduce `h0`.

Establish `h2` using `congrArg Matrix.det (h τ)`. Rewrite `h2` using `[FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul, Matrix.det_diagonal]`. Use `Finset.prod_ne_zero_iff.2 (fun k _ => ?_) h2.symm` and prove the remaining obligations. Apply the tactic sequence `rcases sgn_sq p0 k with h' | h' <;> simp [h']`. Rewrite using `[dmin, h τ, lminor_signature, Complex.ofReal_re]`.

Apply the tactic sequence `rcases psgn_sq p0 i with h' | h' <;> simp [h']`. Rewrite using `[dmin, h τ, lminor_signature]`. Apply the tactic sequence `rcases psgn_sq p0 i with h' | h' <;> simp [h']`. Rewrite using `[FrameDegreeData.gram_mul, FrameDegreeData.gram_eq τ Gm u, hu, FrameDegreeData.gram_eq]`.
-/
theorem unit_frame_eq_orthonormal_mul_triangular :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E), (∀ a b, cc (Gm a b) = Gm b a) → (∀ x ∈ GG Ψ Gm p0, (∀ τ i, ‖dmin Gm x τ i‖ = 1) → ∃ x₀ : Frame Ψ r, ∃ b ∈ Bor Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∀ τ i, ‖b τ i i‖ = 1) ∧ x = rmul x₀ b) ∧ (∀ x₀ : Frame Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → x₀ ∈ GG Ψ Gm p0 ∧ ∀ τ i, ‖dmin Gm x₀ τ i‖ = 1) ∧ ∀ (τ : E →+* ℂ) (u x₀ : Matrix (Fin r) (Fin r) ℂ), uᵀ * Gm.map τ * u.map (starRingEnd ℂ) = Gm.map τ → gram τ Gm (u * x₀) = gram τ Gm x₀ := by
  intro E _ _ _ r p0 Ψ Gm hG
  refine ⟨fun x hx h1 => ?_, fun x₀ h => ⟨fun τ => ⟨?_, fun i => ?_⟩, fun τ i => ?_⟩,
    fun τ u x₀ hu => ?_⟩
  · refine ⟨fun τ => (mat x τ * uMat (gram τ.1 Gm (mat x τ)) : Matrix _ _ ℂ),
      fun τ => ((uMat (gram τ.1 Gm (mat x τ)))⁻¹ : Matrix _ _ ℂ), fun τ => ⟨?_, fun a c hca => ?_⟩,
      fun τ => ?_, fun τ i => ?_, ?_⟩
    · show ((uMat (gram τ.1 Gm (mat x τ)))⁻¹).det ≠ 0
      rw [Matrix.det_nonsing_inv, det_uMat]
      simp
    · exact inv_uMat_upper _ hca
    · show gram τ.1 Gm (mat x τ * uMat (gram τ.1 Gm (mat x τ))) = _
      rw [FrameDegreeData.gram_mul]
      exact uMat_conj_eq_signature p0 _ (gram_isHermitian τ.1 hG _) (hx τ).2 (h1 τ)
    · show ‖(uMat (gram τ.1 Gm (mat x τ)))⁻¹ i i‖ = 1
      rw [inv_uMat_diag, norm_one]
    · funext τ
      show mat x τ = (mat x τ * uMat (gram τ.1 Gm (mat x τ))) * (uMat (gram τ.1 Gm (mat x τ)))⁻¹
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ (by rw [det_uMat]; exact isUnit_one)]
  · intro h0
    have h2 := congrArg Matrix.det (h τ)
    rw [FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
      Matrix.det_diagonal] at h2
    refine Finset.prod_ne_zero_iff.2 (fun k _ => ?_) h2.symm
    rcases sgn_sq p0 k with h' | h' <;> simp [h']
  · rw [dmin, h τ, lminor_signature, Complex.ofReal_re]
    rcases psgn_sq p0 i with h' | h' <;> simp [h']
  · rw [dmin, h τ, lminor_signature]
    rcases psgn_sq p0 i with h' | h' <;> simp [h']
  · rw [FrameDegreeData.gram_mul, FrameDegreeData.gram_eq τ Gm u, hu, FrameDegreeData.gram_eq]

end GlobalTheory.UnitFrames
