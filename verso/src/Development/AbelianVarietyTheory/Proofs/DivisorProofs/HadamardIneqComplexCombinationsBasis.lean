import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Hadamard

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
open Matrix
open scoped ComplexOrder ComplexConjugate

namespace GlobalTheory.HSShort

/- English proof (translation)
Introduce `F V _ _ _ nm d b σ P`. Establish `hG : (nm.gram σ b).PosDef` using `nm.posDef σ d b b.linearIndependent`. Take `⟨hre, him⟩` from `Complex.pos_iff.mp hG.det_pos`. Use `⟨hre, ?_⟩` and prove the remaining obligations. Use `set G := nm.gram σ b with hGdef`.

Establish `hM : (Pᴴ * G * P).PosSemidef` using `hG.posSemidef.conjTranspose_mul_mul_same P`. Establish `h1` using `ReciprocityTheory.ChartRestriction.G.T0.psd_det_re_le_prod_diag d _ hM`. Establish `hdet : (Pᴴ * G * P).det.re = ‖P.det‖ ^ 2 * G.det.re`. Rewrite using `[det_mul, det_mul, det_conjTranspose]`. Establish `: star P.det * G.det * P.det = ((Complex.normSq P.det : ℝ) : ℂ) * G.det`.

Rewrite using `[Complex.normSq_eq_conj_mul_self, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]`. Establish `hdiag : ∀ k, ((Pᴴ * G * P) k k).re = csq nm σ (fun i => P i k) b`. Introduce `k`.

Simplify using `only [csq, Matrix.mul_apply, Matrix.conjTranspose_apply, hGdef, HermFam.gram, Matrix.of_apply, Finset.sum_mul, Complex.star_def]`. Use `congr 1`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h1` using `[hdet]`. Simplify using `only [hdiag] at h1`. Establish `hnn : ∀ k ∈ Finset.univ, 0 ≤ csq nm σ (fun i => P i k) b` using `fun k _ => csq_nonneg nm σ _ _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]`.

Use `_ ≤ Real.sqrt (∏ k, csq nm σ (fun i => P i k) b) := Real.sqrt_le_sqrt h1`. Use `_ = ∏ k, cnrm nm σ (fun i => P i k) b := by`. Rewrite using `[Real.sqrt_prod _ hnn]`. Both sides reduce to the same expression.
-/
theorem hadamard_basis_comb : ∀ (F V : Type) [Field F] [AddCommGroup V] [Module F V] (nm : HermFam F V)
    (d : ℕ) (b : Module.Basis (Fin d) F V) (σ : F →+* ℂ) (P : Matrix (Fin d) (Fin d) ℂ),
    0 < (nm.gram σ b).det.re ∧
      ‖P.det‖ * Real.sqrt (nm.gram σ b).det.re ≤ ∏ k, cnrm nm σ (fun i => P i k) b := by
  intro F V _ _ _ nm d b σ P
  have hG : (nm.gram σ b).PosDef := nm.posDef σ d b b.linearIndependent
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hG.det_pos
  refine ⟨hre, ?_⟩
  set G := nm.gram σ b with hGdef
  have hM : (Pᴴ * G * P).PosSemidef := hG.posSemidef.conjTranspose_mul_mul_same P
  have h1 := ReciprocityTheory.ChartRestriction.G.T0.psd_det_re_le_prod_diag d _ hM
  have hdet : (Pᴴ * G * P).det.re = ‖P.det‖ ^ 2 * G.det.re := by
    rw [det_mul, det_mul, det_conjTranspose]
    have : star P.det * G.det * P.det = ((Complex.normSq P.det : ℝ) : ℂ) * G.det := by
      rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]; ring
    rw [this, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
  have hdiag : ∀ k, ((Pᴴ * G * P) k k).re = csq nm σ (fun i => P i k) b := by
    intro k
    simp only [csq, Matrix.mul_apply, Matrix.conjTranspose_apply, hGdef, HermFam.gram, Matrix.of_apply,
      Finset.sum_mul, Complex.star_def]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hdet] at h1
  simp only [hdiag] at h1
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ csq nm σ (fun i => P i k) b := fun k _ => csq_nonneg nm σ _ _
  calc ‖P.det‖ * Real.sqrt G.det.re = Real.sqrt (‖P.det‖ ^ 2 * G.det.re) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (∏ k, csq nm σ (fun i => P i k) b) := Real.sqrt_le_sqrt h1
    _ = ∏ k, cnrm nm σ (fun i => P i k) b := by
        rw [Real.sqrt_prod _ hnn]; rfl

end GlobalTheory.HSShort
