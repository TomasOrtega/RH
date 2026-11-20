import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergy
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergyInvariant
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergyDiagonal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyCongruence

variable {n : Type*} [Fintype n] [DecidableEq n]

/- English proof (translation)
Introduce `h`. Use `congrArg Matrix.det hU` as an intermediate fact. Rewrite `this` using `[det_mul, h, mul_zero, det_one]`. Conclude with `zero_ne_one this`.
-/
theorem det_ne_zero_of_star_mul_self {U : Matrix n n ℂ} (hU : star U * U = 1) : U.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det hU
  rw [det_mul, h, mul_zero, det_one] at this
  exact zero_ne_one this

/- English proof (translation)
Use `set U : Matrix n n ℂ := (hN.1.eigenvectorUnitary : Matrix n n ℂ) with hUdef`. Use `set μ := hN.1.eigenvalues`. Use `set d : n → ℂ := fun j => (((Real.sqrt (μ j))⁻¹ : ℝ) : ℂ) with hd`. Establish `hU : star U * U = 1` using `Unitary.coe_star_mul_self _`. Establish `hN' : N = U * diagonal (fun j => (μ j : ℂ)) * star U` using `hN.1.spectral_theorem`.

Establish `hμ : ∀ j, 0 < μ j` using `hN.eigenvalues_pos`. Use `⟨U * diagonal d, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[det_mul, det_diagonal]`. Use `mul_ne_zero (det_ne_zero_of_star_mul_self hU) (Finset.prod_ne_zero_iff.mpr fun j _ => ?_)` and prove the remaining obligations. Use `Real.sqrt_pos.mpr (hμ j)` as an intermediate fact.

Simplify using `only [hd, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]`. Conclude with `this.ne'`. Establish `hstar : Uᴴ = star U` using `rfl`. Rewrite using `[hN', conjTranspose_mul, diagonal_conjTranspose, hstar]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by`. Rewrite using `[hU, Matrix.mul_one, Matrix.mul_one, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Establish `hs` using `Real.sqrt_pos.mpr (hμ j)`. Establish `hsq` using `Real.sq_sqrt (hμ j).le`. Simplify using `only [hd, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]`. Rewrite using `[← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_congr_eq_one {N : Matrix n n ℂ} (hN : N.PosDef) :
    ∃ C : Matrix n n ℂ, C.det ≠ 0 ∧ Cᴴ * N * C = 1 := by
  set U : Matrix n n ℂ := (hN.1.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set μ := hN.1.eigenvalues
  set d : n → ℂ := fun j => (((Real.sqrt (μ j))⁻¹ : ℝ) : ℂ) with hd
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hN' : N = U * diagonal (fun j => (μ j : ℂ)) * star U := hN.1.spectral_theorem
  have hμ : ∀ j, 0 < μ j := hN.eigenvalues_pos
  refine ⟨U * diagonal d, ?_, ?_⟩
  · rw [det_mul, det_diagonal]
    refine mul_ne_zero (det_ne_zero_of_star_mul_self hU) (Finset.prod_ne_zero_iff.mpr fun j _ => ?_)
    have := Real.sqrt_pos.mpr (hμ j)
    simp only [hd, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact this.ne'
  · have hstar : Uᴴ = star U := rfl
    rw [hN', conjTranspose_mul, diagonal_conjTranspose, hstar]
    calc diagonal (star d) * star U * (U * diagonal (fun j => (μ j : ℂ)) * star U) * (U * diagonal d)
        = diagonal (star d) * (star U * U) * diagonal (fun j => (μ j : ℂ)) * (star U * U) * diagonal d := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hU, Matrix.mul_one, Matrix.mul_one, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
          congr 1
          funext j
          have hs := Real.sqrt_pos.mpr (hμ j)
          have hsq := Real.sq_sqrt (hμ j).le
          simp only [hd, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
          rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
          congr 1
          field_simp
          linarith

/- English proof (translation)
Rewrite using `[det_mul, det_mul, det_conjTranspose, Complex.normSq_eq_conj_mul_self, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_congr (C X : Matrix n n ℂ) :
    (Cᴴ * X * C).det = (Complex.normSq C.det : ℂ) * X.det := by
  rw [det_mul, det_mul, det_conjTranspose, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

end ChartEnergyCongruence

open ChartEnergyCongruence in

/- English proof (translation)
Introduce `e M N hM hN`. Take `⟨C, hC, hCN⟩` from `exists_congr_eq_one hN`. Establish `hCu : IsUnit C` using `(Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hC)`. Establish `hM' : (Cᴴ * M * C).PosDef` using `hM.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hCu)`. Use `set M' := Cᴴ * M * C with hM'def`.

Use `set V : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := (hM'.1.eigenvectorUnitary : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)`. Use `set Λ := hM'.1.eigenvalues`. Establish `hVV : star V * V = 1` using `Unitary.coe_star_mul_self _`. Establish `hVd : V.det ≠ 0` using `det_ne_zero_of_star_mul_self hVV`. Establish `hdiag : Vᴴ * M' * V = diagonal (fun j => (Λ j : ℂ))`.

Use `hM'.1.conjStarAlgAut_star_eigenvectorUnitary` as an intermediate fact. Rewrite `this` using `[Unitary.conjStarAlgAut_star_apply]`. Conclude with `this`. Establish `hone : Vᴴ * 1 * V = 1` using `by rw [Matrix.mul_one]; exact hVV`. Establish `hterm : ∀ k, chartMixedEnergy M N k = chartMixedEnergy (diagonal fun j => (Λ j : ℂ)) 1 k`.

Introduce `k`. Rewrite using `[← hI e M N C hM hN hC k, hCN, ← hI e M' 1 V hM' PosDef.one hVd k, hdiag, hone]`. Rewrite using `[Finset.sum_congr rfl fun k _ => hterm k, hD e Λ hM'.eigenvalues_pos]`. Establish `hMpos` using `(Complex.pos_iff.mp hM.det_pos).1`. Establish `hNpos` using `(Complex.pos_iff.mp hN.det_pos).1`.

Establish `hns : 0 < Complex.normSq C.det` using `Complex.normSq_pos.mpr hC`. Establish `hM're : M'.det.re = Complex.normSq C.det * M.det.re`. Rewrite using `[hM'def, det_congr, Complex.re_ofReal_mul]`. Establish `hN're : 1 = Complex.normSq C.det * N.det.re`. Use `congrArg Complex.re (det_congr C N)` as an intermediate fact.

Rewrite `this` using `[hCN, det_one, Complex.one_re, Complex.re_ofReal_mul]`. Conclude with `this`. Establish `hprod : M'.det.re = ∏ j, Λ j`. Rewrite using `[hM'.1.det_eq_prod_eigenvalues]`. Express the relevant statement in the definitionally equal form `(∏ j, ((Λ j : ℝ) : ℂ)).re = _`.

Rewrite using `[← Complex.ofReal_prod, Complex.ofReal_re]`. Establish `hlog : ∑ j, Real.log (Λ j) = Real.log M.det.re - Real.log N.det.re`. Rewrite using `[← Real.log_prod fun j _ => (hM'.eigenvalues_pos j).ne', ← hprod, hM're, Real.log_mul hns.ne' hMpos.ne']`. Establish `h1 : Real.log (Complex.normSq C.det) + Real.log N.det.re = 0`. Rewrite using `[← Real.log_mul hns.ne' hNpos.ne', ← hN're, Real.log_one]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hlog]`.
-/
theorem ChartEnergy.proof (hI : ChartEnergyLinearInvariant.Statement) (hD : ChartEnergyDiagonal.Statement) :
    ChartEnergy.Statement := by
  intro e M N hM hN
  obtain ⟨C, hC, hCN⟩ := exists_congr_eq_one hN
  have hCu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hC)
  have hM' : (Cᴴ * M * C).PosDef := hM.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hCu)
  set M' := Cᴴ * M * C with hM'def
  set V : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := (hM'.1.eigenvectorUnitary : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
  set Λ := hM'.1.eigenvalues
  have hVV : star V * V = 1 := Unitary.coe_star_mul_self _
  have hVd : V.det ≠ 0 := det_ne_zero_of_star_mul_self hVV
  have hdiag : Vᴴ * M' * V = diagonal (fun j => (Λ j : ℂ)) := by
    have := hM'.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    exact this
  have hone : Vᴴ * 1 * V = 1 := by rw [Matrix.mul_one]; exact hVV
  have hterm : ∀ k, chartMixedEnergy M N k = chartMixedEnergy (diagonal fun j => (Λ j : ℂ)) 1 k := by
    intro k
    rw [← hI e M N C hM hN hC k, hCN, ← hI e M' 1 V hM' PosDef.one hVd k, hdiag, hone]
  rw [Finset.sum_congr rfl fun k _ => hterm k, hD e Λ hM'.eigenvalues_pos]

  have hMpos := (Complex.pos_iff.mp hM.det_pos).1
  have hNpos := (Complex.pos_iff.mp hN.det_pos).1
  have hns : 0 < Complex.normSq C.det := Complex.normSq_pos.mpr hC
  have hM're : M'.det.re = Complex.normSq C.det * M.det.re := by
    rw [hM'def, det_congr, Complex.re_ofReal_mul]
  have hN're : 1 = Complex.normSq C.det * N.det.re := by
    have := congrArg Complex.re (det_congr C N)
    rw [hCN, det_one, Complex.one_re, Complex.re_ofReal_mul] at this
    exact this
  have hprod : M'.det.re = ∏ j, Λ j := by
    rw [hM'.1.det_eq_prod_eigenvalues]
    change (∏ j, ((Λ j : ℝ) : ℂ)).re = _
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  have hlog : ∑ j, Real.log (Λ j) = Real.log M.det.re - Real.log N.det.re := by
    rw [← Real.log_prod fun j _ => (hM'.eigenvalues_pos j).ne', ← hprod, hM're,
      Real.log_mul hns.ne' hMpos.ne']
    have h1 : Real.log (Complex.normSq C.det) + Real.log N.det.re = 0 := by
      rw [← Real.log_mul hns.ne' hNpos.ne', ← hN're, Real.log_one]
    linarith
  rw [hlog]

end

end GroundTheory.Heights₂.Heights
