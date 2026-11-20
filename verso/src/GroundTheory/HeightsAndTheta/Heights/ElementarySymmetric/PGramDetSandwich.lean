import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.GramDetSandwich
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/- English proof (translation)
Establish `hcM : c ≤ M`. Establish `h3` using `(h1.add h2).diag_nonneg (i := ⟨0, hN⟩)`. Simplify using `only [sub_add_sub_cancel', Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at h3`. Establish `h4 : (0 : ℂ) ≤ ((M - c : ℝ) : ℂ)` using `by push_cast; linear_combination h3`. Combine the linear relations using `[Complex.zero_le_real.mp h4]`.

Establish `hM : 0 < M` using `hc.trans_le hcM`. Establish `hHu : IsUnit H.det` using `(isUnit_iff_isUnit_det H).mp hH.isUnit`. Use `⟨hcM, ?_, ?_⟩` and prove the remaining obligations. Establish `hpos : IsStrictlyPositive H⁻¹` using `hH.inv.isStrictlyPositive`. Establish `hle : H⁻¹ ≤ (M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)` using `h2`.

Use `CStarAlgebra.ringInverse_le_ringInverse hle hpos` as an intermediate fact. Rewrite `this` using `[← nonsing_inv_eq_ringInverse, ← nonsing_inv_eq_ringInverse, nonsing_inv_nonsing_inv _ hHu]`. Establish `hinv : ((M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ = ((M⁻¹ : ℝ) : ℂ) • 1`. Apply `inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[smul_mul_smul_comm, Matrix.one_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ hM.ne', Complex.ofReal_one, one_smul]`.

Rewrite `this` using `[hinv]`. Conclude with `this`. Establish `hpos : IsStrictlyPositive ((c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))` using `(PosDef.one.smul (by exact_mod_cast hc)).isStrictlyPositive`. Establish `hle : (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) ≤ H⁻¹` using `h1`. Use `CStarAlgebra.ringInverse_le_ringInverse hle hpos` as an intermediate fact.

Rewrite `this` using `[← nonsing_inv_eq_ringInverse, ← nonsing_inv_eq_ringInverse, nonsing_inv_nonsing_inv _ hHu]`. Establish `hinv : ((c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ = ((c⁻¹ : ℝ) : ℂ) • 1`. Apply `inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[smul_mul_smul_comm, Matrix.one_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne', Complex.ofReal_one, one_smul]`. Rewrite `this` using `[hinv]`.

Conclude with `this`.
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
Rewrite using `[det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]`.
-/
theorem GramDetSandwich.re_det_ofReal_smul {k : ℕ} (t : ℝ) (X : Matrix (Fin k) (Fin k) ℂ) :
    ((t : ℂ) • X).det.re = t ^ k * X.det.re := by
  rw [det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

/- English proof (translation)
Introduce `N k H A c M hc hH h1 h2`. Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Establish `e1 : Aᴴ * A = 0` using `by ext i j; simp [Matrix.mul_apply]`. Establish `e2 : Aᴴ * H * A = 0` using `by ext i j; simp [Matrix.mul_apply]`. Rewrite using `[e1, e2]`.

Break down `k with _ | k` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[det_zero]`. Take `⟨hcM, hlo, hhi⟩` from `GramDetSandwich.loewner_inv hN H c M hc hH h1 h2`. Establish `hM : 0 < M` using `hc.trans_le hcM`.

Establish `hG : (Aᴴ * A).PosSemidef` using `posSemidef_conjTranspose_mul_self A`. Establish `hlo' : (Aᴴ * H * A - ((M⁻¹ : ℝ) : ℂ) • (Aᴴ * A)).PosSemidef`. Use `hlo.conjTranspose_mul_mul_same A` as an intermediate fact. Rewrite `this` using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]`. Then use the resulting hypothesis. Establish `hhi' : (((c⁻¹ : ℝ) : ℂ) • (Aᴴ * A) - Aᴴ * H * A).PosSemidef`.

Use `hhi.conjTranspose_mul_mul_same A` as an intermediate fact. Rewrite `this` using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]`. Then use the resulting hypothesis. Establish `k1` using `MCDet.re_det_mono (hG.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hM.le))) hlo'`. Establish `k2` using `MCDet.re_det_mono (hH.posSemidef.conjTranspose_mul_mul_same A) hhi'`. Simplify using `only [RCLike.re_to_complex] at k1 k2`.

Rewrite `k1`, `k2` using `[GramDetSandwich.re_det_ofReal_smul]`. Conclude with `⟨k1, k2⟩`.
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
