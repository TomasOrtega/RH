import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.DecaysZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Abstract
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ConvCoef
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ContinuousAverage
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.InvMemFlagN
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.FlagNW
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroupStatement

open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

/- English proof (translation)
Introduce `n ε H _ _ σ hσ v a hvv hav W hW ν hν x y`. Take `⟨hc, hn, hU, hI, hS⟩` from `hσ`. Take `⟨d, hd⟩` from `GlobalTheory.T.schur_orthogonality_indefiniteUnitaryGroup n ε H σ hU hI hS`. Establish `hd0 : 0 < d` using `hd.1`. Distinguish the cases in `hv : v = 0`.

Substitute `hv` using the available equality. Simplify using the standard rewrite rules. Establish `hv2 : (‖v‖ : ℝ) ^ 2 ≠ 0` using `by positivity`. Take `⟨hcvv, hconvvv⟩` from `conv_coef n ε H σ d hU hd v v`. Take `⟨hcav, hconvav⟩` from `conv_coef n ε H σ d hU hd v a`.

Take `⟨hivv, -⟩` from `continuous_average n ε _ hcvv hvv`. Take `⟨hiav, hcontav⟩` from `continuous_average n ε _ hcav hav`. Take `⟨hν0, hνf, hνN, hνinv⟩` from `hν`. Use `haveI := hνf`. Take `⟨hflag, h1, hNeq, S, hS⟩` from `flagN_eq_NW n ε W hW`.

Take `⟨r, Hr, hr⟩` from `exists_isRay n ε _ _ hflag (fun i => by fin_cases i; simpa using h1)`. Rewrite `hr` using `[hNeq]`. Use `set k : ℂ := ((d / ‖v‖ ^ 2 : ℝ) : ℂ) with hk`. Establish `hkc : k * ((‖v‖ ^ 2 / d : ℝ) : ℂ) = 1`. Rewrite using `[hk, ← Complex.ofReal_mul]`.

Rewrite using `[div_mul_div_comm, mul_comm d, div_self (mul_ne_zero hv2 hd0.ne')]`. Simplify using the standard rewrite rules. Establish `key` using `average_eq_zero (UJ ε) (muG ε) (NW ε W) r Hr ν hνN hνinv hr (fun g => k * coefOn σ v v g) (coefOn σ a v) (continuous_const.mul hcvv) (hivv.const_mul k) hcav hiav (by`. Introduce `z`. Simplify using `only [conv] at hconvvv ⊢`.

Use `hconvvv z` as an intermediate fact. Simplify using `only [mul_assoc]`. Rewrite using `[show (fun g => k * (coefOn σ v v g * (k * coefOn σ v v (g⁻¹ * z)))) = fun g => (k * k) * (coefOn σ v v g * coefOn σ v v (g⁻¹ * z)) by`. Use function extensionality and compare the values at `g`. Use the proof step `ring]`.

Rewrite using `[MeasureTheory.integral_const_mul, this]`. Take the linear combination `(k * coefOn σ v v z) * hkc)`. Use the proof step `(by`. Introduce `z`. Simplify using `only [conv] at hconvav ⊢`.

Use `hconvav z` as an intermediate fact. Simplify using `only [mul_assoc]`. Rewrite using `[MeasureTheory.integral_const_mul, this]`. Take the linear combination `(coefOn σ a v z) * hkc)`. Use `x (hcontav S ν (by rw [hS]; exact ⟨hν0, hνf, hνN, hνinv⟩) x) y`.

Conclude with `key`.
-/
theorem UpperTheory.Lit.Cusp.integral_coef_eq_zero :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsSqIntIrr ε σ → ∀ v a : H,
        Decays (coefOn (ε := ε) σ v v) → Decays (coefOn (ε := ε) σ a v) →
        ∀ W, IsIsoC ε W → ∀ ν : Measure (UJ ε), IsHaarSub (NW ε W) ν → ∀ x y : UJ ε,
          ∫ m, ⟪v, σ (umat (x * m * y)) a⟫_ℂ ∂ν = 0 := by
  intro n ε H _ _ σ hσ v a hvv hav W hW ν hν x y
  obtain ⟨hc, hn, hU, hI, hS⟩ := hσ
  obtain ⟨d, hd⟩ := GlobalTheory.T.schur_orthogonality_indefiniteUnitaryGroup n ε H σ hU hI hS
  have hd0 : 0 < d := hd.1
  by_cases hv : v = 0
  · subst hv
    simp
  have hv2 : (‖v‖ : ℝ) ^ 2 ≠ 0 := by positivity
  obtain ⟨hcvv, hconvvv⟩ := conv_coef n ε H σ d hU hd v v
  obtain ⟨hcav, hconvav⟩ := conv_coef n ε H σ d hU hd v a
  obtain ⟨hivv, -⟩ := continuous_average n ε _ hcvv hvv
  obtain ⟨hiav, hcontav⟩ := continuous_average n ε _ hcav hav
  obtain ⟨hν0, hνf, hνN, hνinv⟩ := hν
  haveI := hνf
  obtain ⟨hflag, h1, hNeq, S, hS⟩ := flagN_eq_NW n ε W hW
  obtain ⟨r, Hr, hr⟩ := exists_isRay n ε _ _ hflag (fun i => by fin_cases i; simpa using h1)
  rw [hNeq] at hr
  set k : ℂ := ((d / ‖v‖ ^ 2 : ℝ) : ℂ) with hk
  have hkc : k * ((‖v‖ ^ 2 / d : ℝ) : ℂ) = 1 := by
    rw [hk, ← Complex.ofReal_mul]
    rw [div_mul_div_comm, mul_comm d, div_self (mul_ne_zero hv2 hd0.ne')]
    simp
  have key := average_eq_zero (UJ ε) (muG ε) (NW ε W) r Hr ν hνN hνinv hr
    (fun g => k * coefOn σ v v g) (coefOn σ a v)
    (continuous_const.mul hcvv) (hivv.const_mul k) hcav hiav
    (by
      intro z
      simp only [conv] at hconvvv ⊢
      have := hconvvv z
      simp only [mul_assoc]
      rw [show (fun g => k * (coefOn σ v v g * (k * coefOn σ v v (g⁻¹ * z))))
          = fun g => (k * k) * (coefOn σ v v g * coefOn σ v v (g⁻¹ * z)) by
            funext g; ring]
      rw [MeasureTheory.integral_const_mul, this]
      linear_combination (k * coefOn σ v v z) * hkc)
    (by
      intro z
      simp only [conv] at hconvav ⊢
      have := hconvav z
      simp only [mul_assoc]
      rw [MeasureTheory.integral_const_mul, this]
      linear_combination (coefOn σ a v z) * hkc)
    x (hcontav S ν (by rw [hS]; exact ⟨hν0, hνf, hνN, hνinv⟩) x) y
  exact key
