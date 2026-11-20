import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section

open Matrix

open scoped ComplexOrder

namespace Formalism.L2.SG.Pf.Tau

/- English proof (translation)
Simplify using `only [dotProduct, Pi.star_apply, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Simplify using `[Complex.mul_re]`.
-/
theorem re_star_dotProduct_self {m : ℕ} (z : Fin m → ℂ) :
    (star z ⬝ᵥ z).re = ∑ i, ‖z i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]`.
-/
theorem star_dotProduct_gram {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ) (z : Fin k → ℂ) :
    star z ⬝ᵥ ((Aᴴ * A) *ᵥ z) = star (A *ᵥ z) ⬝ᵥ (A *ᵥ z) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

/- English proof (translation)
Establish `key : ∀ i, a ≤ hM.eigenvalues i ∧ hM.eigenvalues i ≤ b`. Introduce `i`. Use `set v : Fin j → ℂ := (hM.eigenvectorBasis i).ofLp with hv_def`. Establish `hnorm : ∑ k, ‖v k‖ ^ 2 = 1`. Establish `h1` using `(hM.eigenvectorBasis).norm_eq_one i`.

Rewrite `h1` using `[EuclideanSpace.norm_eq]`. Establish `h2` using `congrArg (fun t : ℝ => t ^ 2) h1`. Simplify using `only [one_pow] at h2`. Rewrite `h2` using `[Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]`. Then use the resulting hypothesis. Establish `e : (star v ⬝ᵥ (M *ᵥ v)).re = hM.eigenvalues i`.

Rewrite using `[hv_def, hM.mulVec_eigenvectorBasis i, dotProduct_smul, Complex.smul_re, smul_eq_mul, ← hv_def, re_star_dotProduct_self, hnorm, mul_one]`. Use `h v` as an intermediate fact. Rewrite `this` using `[e, hnorm, mul_one, mul_one]`. Conclude with `this`. Use `⟨∏ i, hM.eigenvalues i, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hM.det_eq_prod_eigenvalues]`. Use `norm_cast`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem det_bounds_of_rayleigh {j : ℕ} (M : Matrix (Fin j) (Fin j) ℂ) (hM : M.IsHermitian) (a b : ℝ)
    (ha : 0 ≤ a)
    (h : ∀ z : Fin j → ℂ, a * ∑ i, ‖z i‖ ^ 2 ≤ (star z ⬝ᵥ (M *ᵥ z)).re ∧
      (star z ⬝ᵥ (M *ᵥ z)).re ≤ b * ∑ i, ‖z i‖ ^ 2) :
    ∃ μ : ℝ, M.det = μ ∧ a ^ j ≤ μ ∧ μ ≤ b ^ j := by
  have key : ∀ i, a ≤ hM.eigenvalues i ∧ hM.eigenvalues i ≤ b := by
    intro i
    set v : Fin j → ℂ := (hM.eigenvectorBasis i).ofLp with hv_def
    have hnorm : ∑ k, ‖v k‖ ^ 2 = 1 := by
      have h1 := (hM.eigenvectorBasis).norm_eq_one i
      rw [EuclideanSpace.norm_eq] at h1
      have h2 := congrArg (fun t : ℝ => t ^ 2) h1
      simp only [one_pow] at h2
      rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h2
    have e : (star v ⬝ᵥ (M *ᵥ v)).re = hM.eigenvalues i := by
      rw [hv_def, hM.mulVec_eigenvectorBasis i, dotProduct_smul, Complex.smul_re, smul_eq_mul,
        ← hv_def, re_star_dotProduct_self, hnorm, mul_one]
    have := h v
    rw [e, hnorm, mul_one, mul_one] at this
    exact this
  refine ⟨∏ i, hM.eigenvalues i, ?_, ?_, ?_⟩
  · rw [hM.det_eq_prod_eigenvalues]
    norm_cast
  · calc a ^ j = ∏ _i : Fin j, a := by simp
      _ ≤ ∏ i, hM.eigenvalues i := Finset.prod_le_prod (fun _ _ => ha) (fun i _ => (key i).1)
  · calc ∏ i, hM.eigenvalues i ≤ ∏ _i : Fin j, b :=
          Finset.prod_le_prod (fun i _ => ha.trans (key i).1) (fun i _ => (key i).2)
      _ = b ^ j := by simp

/- English proof (translation)
Establish `hH` using `hG.isHermitian`. Use `set U : Matrix (Fin j) (Fin j) ℂ := (hH.eigenvectorUnitary : Matrix (Fin j) (Fin j) ℂ) with hU_def`. Establish `hU : star U * U = 1` using `by simp [U]`. Establish `hspec : G = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U`. Use `hH.spectral_theorem` as an intermediate fact.

Rewrite `this` using `[Unitary.conjStarAlgAut_apply]`. Then use the resulting hypothesis. Establish `hpos : ∀ i, 0 < hH.eigenvalues i` using `hG.eigenvalues_pos`. Use `⟨diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U, ?_⟩` and prove the remaining obligations. Rewrite using `[show (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U) * G * (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U)ᴴ = (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U) * (U * diagonal (RCLike.ofReal ∘ hH.e …`. Rewrite using `[conjTranspose_mul, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul, ← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `hs : 0 < Real.sqrt (hH.eigenvalues i)` using `Real.sqrt_pos.2 (hpos i)`.

Establish `hsq : Real.sqrt (hH.eigenvalues i) ^ 2 = hH.eigenvalues i` using `Real.sq_sqrt (hpos i).le`. Establish `h1 : (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i))⁻¹ = 1`. Rewrite using `[show (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i))⁻¹ = hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i) ^ 2)⁻¹ by ring, hsq, mul_inv_cancel₀ (hpos i).ne']`. Simplify using `only [Function.comp, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]`. Rewrite using `[← mul_assoc]`.

Establish `h2` using `congrArg (fun t : ℝ => (t : ℂ)) h1`. Move the coercions through the operations in `at h2`. Simplify using `using h2`.
-/
theorem exists_mul_mul_conjTranspose_eq_one {j : ℕ} {G : Matrix (Fin j) (Fin j) ℂ} (hG : G.PosDef) :
    ∃ S : Matrix (Fin j) (Fin j) ℂ, S * G * Sᴴ = 1 := by
  have hH := hG.isHermitian
  set U : Matrix (Fin j) (Fin j) ℂ := (hH.eigenvectorUnitary : Matrix (Fin j) (Fin j) ℂ) with hU_def
  have hU : star U * U = 1 := by simp [U]
  have hspec : G = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    have := hH.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at this
  have hpos : ∀ i, 0 < hH.eigenvalues i := hG.eigenvalues_pos
  refine ⟨diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U, ?_⟩
  rw [show (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U) * G *
      (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U)ᴴ =
      (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U) *
      (U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U) *
      (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U)ᴴ by rw [← hspec]]
  rw [conjTranspose_mul, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose,
    ← Matrix.star_eq_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul, ← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  have hs : 0 < Real.sqrt (hH.eigenvalues i) := Real.sqrt_pos.2 (hpos i)
  have hsq : Real.sqrt (hH.eigenvalues i) ^ 2 = hH.eigenvalues i := Real.sq_sqrt (hpos i).le
  have h1 : (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i))⁻¹ = 1 := by
    rw [show (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i))⁻¹
        = hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i) ^ 2)⁻¹ by ring, hsq, mul_inv_cancel₀ (hpos i).ne']
  simp only [Function.comp, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
  rw [← mul_assoc]
  have h2 := congrArg (fun t : ℝ => (t : ℂ)) h1
  push_cast at h2
  simpa using h2

/- English proof (translation)
Take `⟨z, hz0, hz⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hd`. Establish `hCz : C *ᵥ z = 0`. Establish `h1 : star z ⬝ᵥ ((Cᴴ * C) *ᵥ z) = 0` using `by rw [hz, dotProduct_zero]`. Rewrite `h1` using `[star_dotProduct_gram]`. Conclude with `dotProduct_star_self_eq_zero.mp h1`.

Apply `Matrix.exists_mulVec_eq_zero_iff.mp` to reduce the goal to its premises. Use `⟨z, hz0, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hCz, Matrix.mulVec_zero, Matrix.mulVec_zero]`.
-/
theorem det_gram_mul_eq_zero {n j : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin j) ℂ)
    (hd : (Cᴴ * C).det = 0) : ((Y * C)ᴴ * (Y * C)).det = 0 := by
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have hCz : C *ᵥ z = 0 := by
    have h1 : star z ⬝ᵥ ((Cᴴ * C) *ᵥ z) = 0 := by rw [hz, dotProduct_zero]
    rw [star_dotProduct_gram] at h1
    exact dotProduct_star_self_eq_zero.mp h1
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨z, hz0, ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hCz, Matrix.mulVec_zero, Matrix.mulVec_zero]

/- English proof (translation)
Introduce `n j Y C a b ha hY`. Distinguish the cases in `hd : (Cᴴ * C).det = 0`. Rewrite using `[hd, det_gram_mul_eq_zero Y C hd]`. Simplify using the standard rewrite rules. Establish `hPS : (Cᴴ * C).PosSemidef` using `Matrix.posSemidef_conjTranspose_mul_self C`.

Establish `hPD : (Cᴴ * C).PosDef` using `hPS.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))`. Take `⟨S, hS⟩` from `exists_mul_mul_conjTranspose_eq_one hPD`. Use `set V := C * Sᴴ with hV_def`. Establish `hV : Vᴴ * V = 1`. Rewrite using `[hV_def, conjTranspose_mul, conjTranspose_conjTranspose]`.

Rewrite using `[show S * Cᴴ * (C * Sᴴ) = S * (Cᴴ * C) * Sᴴ by simp only [Matrix.mul_assoc]]`. Conclude with `hS`. Use `set M := (Y * V)ᴴ * (Y * V) with hM_def`. Establish `hMH : M.IsHermitian` using `Matrix.isHermitian_conjTranspose_mul_self _`. Establish `hray : ∀ z : Fin j → ℂ, a * ∑ i, ‖z i‖ ^ 2 ≤ (star z ⬝ᵥ (M *ᵥ z)).re ∧ (star z ⬝ᵥ (M *ᵥ z)).re ≤ b * ∑ i, ‖z i‖ ^ 2`.

Introduce `z`. Establish `e1 : (star z ⬝ᵥ (M *ᵥ z)).re = ∑ i, ‖((Y * V) *ᵥ z) i‖ ^ 2`. Rewrite using `[hM_def, star_dotProduct_gram, re_star_dotProduct_self]`. Establish `e2 : ∑ i, ‖(V *ᵥ z) i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2`. Rewrite using `[← re_star_dotProduct_self, ← star_dotProduct_gram, hV, Matrix.one_mulVec, re_star_dotProduct_self]`.

Use `hY (V *ᵥ z)` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, e2]`. Rewrite using `[e1]`. Conclude with `this`. Take `⟨μ, hμ, h1, h2⟩` from `det_bounds_of_rayleigh M hMH a b ha hray`.

Establish `hMeq : M = S * ((Y * C)ᴴ * (Y * C)) * Sᴴ`. Simplify using `only [hM_def, hV_def, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]`. Establish `hdet1 : S.det * (Cᴴ * C).det * Sᴴ.det = 1`. Rewrite using `[← det_mul, ← det_mul, hS, det_one]`. Establish `hdY : ((Y * C)ᴴ * (Y * C)).det = μ * (Cᴴ * C).det`.

Combine the equalities or inequalities in the displayed calculation. Establish `hG0` using `hPS.det_nonneg`. Rewrite `hG0` using `[Complex.nonneg_iff]`. Establish `hre : ((Y * C)ᴴ * (Y * C)).det.re = μ * (Cᴴ * C).det.re`. Rewrite using `[hdY, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]`.

Rewrite using `[hre]`. Conclude with `⟨mul_le_mul_of_nonneg_right h1 hG0.1, mul_le_mul_of_nonneg_right h2 hG0.1⟩`.
-/
theorem t5 : GramDistortionBound := by
  intro n j Y C a b ha hY
  by_cases hd : (Cᴴ * C).det = 0
  · rw [hd, det_gram_mul_eq_zero Y C hd]
    simp
  have hPS : (Cᴴ * C).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self C
  have hPD : (Cᴴ * C).PosDef := hPS.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  obtain ⟨S, hS⟩ := exists_mul_mul_conjTranspose_eq_one hPD
  set V := C * Sᴴ with hV_def
  have hV : Vᴴ * V = 1 := by
    rw [hV_def, conjTranspose_mul, conjTranspose_conjTranspose]
    rw [show S * Cᴴ * (C * Sᴴ) = S * (Cᴴ * C) * Sᴴ by simp only [Matrix.mul_assoc]]
    exact hS
  set M := (Y * V)ᴴ * (Y * V) with hM_def
  have hMH : M.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self _
  have hray : ∀ z : Fin j → ℂ, a * ∑ i, ‖z i‖ ^ 2 ≤ (star z ⬝ᵥ (M *ᵥ z)).re ∧
      (star z ⬝ᵥ (M *ᵥ z)).re ≤ b * ∑ i, ‖z i‖ ^ 2 := by
    intro z
    have e1 : (star z ⬝ᵥ (M *ᵥ z)).re = ∑ i, ‖((Y * V) *ᵥ z) i‖ ^ 2 := by
      rw [hM_def, star_dotProduct_gram, re_star_dotProduct_self]
    have e2 : ∑ i, ‖(V *ᵥ z) i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
      rw [← re_star_dotProduct_self, ← star_dotProduct_gram, hV, Matrix.one_mulVec, re_star_dotProduct_self]
    have := hY (V *ᵥ z)
    rw [Matrix.mulVec_mulVec, e2] at this
    rw [e1]
    exact this
  obtain ⟨μ, hμ, h1, h2⟩ := det_bounds_of_rayleigh M hMH a b ha hray
  have hMeq : M = S * ((Y * C)ᴴ * (Y * C)) * Sᴴ := by
    simp only [hM_def, hV_def, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hdet1 : S.det * (Cᴴ * C).det * Sᴴ.det = 1 := by
    rw [← det_mul, ← det_mul, hS, det_one]
  have hdY : ((Y * C)ᴴ * (Y * C)).det = μ * (Cᴴ * C).det := by
    calc ((Y * C)ᴴ * (Y * C)).det
        = ((Y * C)ᴴ * (Y * C)).det * (S.det * (Cᴴ * C).det * Sᴴ.det) := by rw [hdet1, mul_one]
      _ = (S.det * ((Y * C)ᴴ * (Y * C)).det * Sᴴ.det) * (Cᴴ * C).det := by ring
      _ = μ * (Cᴴ * C).det := by rw [← det_mul, ← det_mul, ← hMeq, hμ]
  have hG0 := hPS.det_nonneg
  rw [Complex.nonneg_iff] at hG0
  have hre : ((Y * C)ᴴ * (Y * C)).det.re = μ * (Cᴴ * C).det.re := by
    rw [hdY, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hre]
  exact ⟨mul_le_mul_of_nonneg_right h1 hG0.1, mul_le_mul_of_nonneg_right h2 hG0.1⟩

end Formalism.L2.SG.Pf.Tau
