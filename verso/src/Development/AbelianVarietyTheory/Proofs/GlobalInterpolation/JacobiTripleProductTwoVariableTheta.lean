import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultipliableTpFactor
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleFiniteProductStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleProductLimitStatement

open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.JacobiTriple

/- English proof (translation)
Introduce `τ z`. Use `set s := cexp (π * I * (τ : ℂ)) with hs`. Use `set x := cexp (2 * π * I * z) with hx`. Establish `hτ : 0 < (τ : ℂ).im` using `τ.2`. Establish `hs1 : ‖s‖ < 1` using `norm_exp_pi_I_lt_one (τ : ℂ) hτ`.

Establish `hs0 : s ≠ 0` using `exp_ne_zero _`. Establish `hx0 : x ≠ 0` using `exp_ne_zero _`. Establish `ht1 : ‖s ^ 2‖ < 1`. Rewrite using `[norm_pow]`. Use polynomial arithmetic with `[norm_nonneg s]`.

Take `⟨hP, hP0, -⟩` from `qPoch_tendsto (s ^ 2) ht1`. Establish `hT` using `GlobalTheory.T.jacobi_triple_product_limit (τ : ℂ) z hτ`. Rewrite using `[(multipliable_tpFactor τ z).hasProd_iff_tendsto_nat]`. Establish `key : ∀ n : ℕ, ∏ k ∈ Finset.range n, GlobalTheory.ThetaWeberRoad.tpFactor τ z k = qPoch (s ^ 2) n * ∑ j ∈ Finset.Icc (-(n : ℤ)) n, finCoeff (cexp (π * I * (τ : ℂ)) ^ 2) n j * jacobiTheta₂_term j z τ`. Introduce `n`.

Rewrite using `[Finset.prod_congr rfl (fun k _ => tpFactor_eq τ z k), Finset.prod_mul_distrib]`. Establish `hf` using `GlobalTheory.T.jacobiTriple_finite_product s x hs0 hs1 hx0 n`. Simplify using `only [hs, hx] at hf`. Simplify using `only [hf, jacobiTheta₂_term_eq_zpow]`. Both sides reduce to the same expression.

Repeatedly rewrite using `[key]`. Use `hP.mul hT` as an intermediate fact. Rewrite `this` using `[mul_left_comm, mul_inv_cancel₀ hP0, mul_one]`. Then use the resulting hypothesis.
-/
theorem tripleProduct : GlobalTheory.ThetaWeberRoad.TripleProduct := by
  intro τ z
  set s := cexp (π * I * (τ : ℂ)) with hs
  set x := cexp (2 * π * I * z) with hx
  have hτ : 0 < (τ : ℂ).im := τ.2
  have hs1 : ‖s‖ < 1 := norm_exp_pi_I_lt_one (τ : ℂ) hτ
  have hs0 : s ≠ 0 := exp_ne_zero _
  have hx0 : x ≠ 0 := exp_ne_zero _
  have ht1 : ‖s ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg s]
  obtain ⟨hP, hP0, -⟩ := qPoch_tendsto (s ^ 2) ht1
  have hT := GlobalTheory.T.jacobi_triple_product_limit (τ : ℂ) z hτ
  rw [(multipliable_tpFactor τ z).hasProd_iff_tendsto_nat]
  have key : ∀ n : ℕ, ∏ k ∈ Finset.range n, GlobalTheory.ThetaWeberRoad.tpFactor τ z k =
      qPoch (s ^ 2) n * ∑ j ∈ Finset.Icc (-(n : ℤ)) n,
        finCoeff (cexp (π * I * (τ : ℂ)) ^ 2) n j * jacobiTheta₂_term j z τ := by
    intro n
    rw [Finset.prod_congr rfl (fun k _ => tpFactor_eq τ z k), Finset.prod_mul_distrib]
    have hf := GlobalTheory.T.jacobiTriple_finite_product s x hs0 hs1 hx0 n
    simp only [hs, hx] at hf
    simp only [hf, jacobiTheta₂_term_eq_zpow]
    rfl
  simp_rw [key]
  have := hP.mul hT
  rwa [mul_left_comm, mul_inv_cancel₀ hP0, mul_one] at this

end GlobalTheory.JacobiTriple
