import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.GramDetSandwich
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem GramDetSandwich.loewner_inv {N : ℕ} (hN : 0 < N) (H : Matrix (Fin N) (Fin N) ℂ) (c M : ℝ)
    (hc : 0 < c) (hH : H.PosDef)
    (h1 : (H⁻¹ - (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef)
    (h2 : ((M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - H⁻¹).PosSemidef) :
    c ≤ M ∧ (H - ((M⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef ∧
      (((c⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - H).PosSemidef := by
  have hcM : c ≤ M := by
    have h3 := (h1.add h2).diag_nonneg (i := ⟨0, hN⟩)
    simp only [sub_add_sub_cancel', Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul,
      mul_one] at h3
    have h4 : (0 : ℂ) ≤ ((M - c : ℝ) : ℂ) := by push_cast; linear_combination h3
    linarith [Complex.zero_le_real.mp h4]
  have hM : 0 < M := hc.trans_le hcM
  have hHu : IsUnit H.det := (isUnit_iff_isUnit_det H).mp hH.isUnit
  refine ⟨hcM, ?_, ?_⟩
  · have hpos : IsStrictlyPositive H⁻¹ := hH.inv.isStrictlyPositive
    have hle : H⁻¹ ≤ (M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := h2
    have := CStarAlgebra.ringInverse_le_ringInverse hle hpos
    rw [← nonsing_inv_eq_ringInverse, ← nonsing_inv_eq_ringInverse, nonsing_inv_nonsing_inv _ hHu] at this
    have hinv : ((M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ = ((M⁻¹ : ℝ) : ℂ) • 1 := by
      apply inv_eq_left_inv
      rw [smul_mul_smul_comm, Matrix.one_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ hM.ne',
        Complex.ofReal_one, one_smul]
    rw [hinv] at this
    exact this
  · have hpos : IsStrictlyPositive ((c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
      (PosDef.one.smul (by exact_mod_cast hc)).isStrictlyPositive
    have hle : (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) ≤ H⁻¹ := h1
    have := CStarAlgebra.ringInverse_le_ringInverse hle hpos
    rw [← nonsing_inv_eq_ringInverse, ← nonsing_inv_eq_ringInverse, nonsing_inv_nonsing_inv _ hHu] at this
    have hinv : ((c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ = ((c⁻¹ : ℝ) : ℂ) • 1 := by
      apply inv_eq_left_inv
      rw [smul_mul_smul_comm, Matrix.one_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne',
        Complex.ofReal_one, one_smul]
    rw [hinv] at this
    exact this

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem GramDetSandwich.re_det_ofReal_smul {k : ℕ} (t : ℝ) (X : Matrix (Fin k) (Fin k) ℂ) :
    ((t : ℂ) • X).det.re = t ^ k * X.det.re := by
  rw [det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components.
-/
theorem GramDetSandwich.proof : GramDetSandwich.Statement := by
  intro N k H A c M hc hH h1 h2
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have e1 : Aᴴ * A = 0 := by ext i j; simp [Matrix.mul_apply]
    have e2 : Aᴴ * H * A = 0 := by ext i j; simp [Matrix.mul_apply]
    rw [e1, e2]
    rcases k with _ | k
    · simp
    · simp [det_zero]
  obtain ⟨hcM, hlo, hhi⟩ := GramDetSandwich.loewner_inv hN H c M hc hH h1 h2
  have hM : 0 < M := hc.trans_le hcM
  have hG : (Aᴴ * A).PosSemidef := posSemidef_conjTranspose_mul_self A
  have hlo' : (Aᴴ * H * A - ((M⁻¹ : ℝ) : ℂ) • (Aᴴ * A)).PosSemidef := by
    have := hlo.conjTranspose_mul_mul_same A
    rwa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at this
  have hhi' : (((c⁻¹ : ℝ) : ℂ) • (Aᴴ * A) - Aᴴ * H * A).PosSemidef := by
    have := hhi.conjTranspose_mul_mul_same A
    rwa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at this
  have k1 := MCDet.re_det_mono (hG.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hM.le))) hlo'
  have k2 := MCDet.re_det_mono (hH.posSemidef.conjTranspose_mul_mul_same A) hhi'
  simp only [RCLike.re_to_complex] at k1 k2
  rw [GramDetSandwich.re_det_ofReal_smul] at k1 k2
  exact ⟨k1, k2⟩

end GroundTheory.Heights₂.Heights.NineStatements
