import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

noncomputable section

namespace PGaussPoissonDual

/- English proof (translation)
Rewrite using `[qf, qf, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]`.
-/
theorem qf_smul {g : ℕ} (c : ℝ) (Y : Matrix (Fin g) (Fin g) ℝ) (w : Fin g → ℝ) :
    qf (c • Y) w = c * qf Y w := by
  rw [qf, qf, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Rewrite using `[qf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w Bᵀ, Matrix.vecMul_transpose]`.
-/
theorem dot_mulVec_self {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (w : Fin g → ℝ) :
    (B *ᵥ w) ⬝ᵥ (B *ᵥ w) = qf (Bᵀ * B) w := by
  rw [qf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w Bᵀ, Matrix.vecMul_transpose]

end PGaussPoissonDual

open PGaussPoissonDual in

/- English proof (translation)
Introduce `g Y ρ hY hρ hmin u`. Establish `hY2 : ((1 / 2 : ℝ) • Y).PosDef` using `hY.smul (by norm_num)`. Take `⟨B, hB⟩` from `hS g _ hY2`. Establish `hdetB : B.det ≠ 0`. Introduce `h0`.

Establish `h1 : (Bᵀ * B).det = 0` using `by rw [det_mul, det_transpose, h0, mul_zero]`. Rewrite `h1` using `[hB]`. Conclude with `hY2.det_pos.ne' h1`. Establish `hterm : ∀ k : Fin g → ℤ, Real.exp (-(π / 2) * qf Y (intVec k + u)) = Real.exp (-π * ((B *ᵥ (intVec k + u)) ⬝ᵥ (B *ᵥ (intVec k + u))))`. Introduce `k`.

Rewrite using `[dot_mulVec_self, hB, qf_smul]`. Put the polynomial expressions in normal form. Take `⟨hsum, -, hle⟩` from `hP g B hdetB u`. Use `⟨(summable_congr hterm).2 hsum, GroundTheory.Global.dualLattice (gaussLattice B), ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv hv0`.

Take `⟨l, hl0, hl⟩` from `hM g B hdetB v hv hv0`. Establish `hYdet : IsUnit Y.det` using `isUnit_iff_ne_zero.2 hY.det_pos.ne'`. Establish `hinv : (Bᵀ * B)⁻¹ = (2 : ℝ) • Y⁻¹`. Rewrite using `[hB]`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises.

Rewrite using `[smul_mul_smul_comm, Y.nonsing_inv_mul hYdet]`. Evaluate the numerical expressions. Rewrite `hl` using `[hinv, qf_smul]`. Establish `h2` using `hmin l hl0`. Establish `hq : 0 ≤ qf Y⁻¹ (intVec l)` using `le_trans (sq_nonneg ρ) h2`.

Establish `h3 : ρ ^ 2 ≤ ‖v‖ ^ 2` using `by linarith`. Use polynomial arithmetic with `[norm_nonneg v]`. Rewrite using `[tsum_congr hterm, ← hD g Y B hY hB]`. Conclude with `hle`.
-/
theorem GaussPoissonDual.proof (hS : GaussSqrt.Statement) (hP : GaussPoissonBound.Statement)
    (hM : GaussDualMin.Statement) (hD : GaussDetFactor.Statement) :
    GaussPoissonDual.Statement := by
  intro g Y ρ hY hρ hmin u
  have hY2 : ((1 / 2 : ℝ) • Y).PosDef := hY.smul (by norm_num)
  obtain ⟨B, hB⟩ := hS g _ hY2
  have hdetB : B.det ≠ 0 := by
    intro h0
    have h1 : (Bᵀ * B).det = 0 := by rw [det_mul, det_transpose, h0, mul_zero]
    rw [hB] at h1
    exact hY2.det_pos.ne' h1
  have hterm : ∀ k : Fin g → ℤ, Real.exp (-(π / 2) * qf Y (intVec k + u)) =
      Real.exp (-π * ((B *ᵥ (intVec k + u)) ⬝ᵥ (B *ᵥ (intVec k + u)))) := by
    intro k
    rw [dot_mulVec_self, hB, qf_smul]
    ring_nf
  obtain ⟨hsum, -, hle⟩ := hP g B hdetB u
  refine ⟨(summable_congr hterm).2 hsum, GroundTheory.Global.dualLattice (gaussLattice B), ?_, ?_⟩
  · intro v hv hv0
    obtain ⟨l, hl0, hl⟩ := hM g B hdetB v hv hv0
    have hYdet : IsUnit Y.det := isUnit_iff_ne_zero.2 hY.det_pos.ne'
    have hinv : (Bᵀ * B)⁻¹ = (2 : ℝ) • Y⁻¹ := by
      rw [hB]
      apply Matrix.inv_eq_left_inv
      rw [smul_mul_smul_comm, Y.nonsing_inv_mul hYdet]
      norm_num
    rw [hinv, qf_smul] at hl
    have h2 := hmin l hl0
    have hq : 0 ≤ qf Y⁻¹ (intVec l) := le_trans (sq_nonneg ρ) h2
    have h3 : ρ ^ 2 ≤ ‖v‖ ^ 2 := by linarith
    nlinarith [norm_nonneg v]
  · rw [tsum_congr hterm, ← hD g Y B hY hB]
    exact hle

end

end GroundTheory.Heights₂.Heights
