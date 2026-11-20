import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinConstantTermPartDifferentiableOn
import ReciprocityTheory.Chebotarev.EulerSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleXSqAddOne
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound

/- English proof (translation)
Establish `h1 : (0 : ℝ) < 1 + ‖w‖ ^ 2` using `by positivity`. Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ h1]`. Establish `hw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2` using `by rw [Complex.sq_norm, Complex.normSq_apply]; ring`. Establish `hn : ‖(a : ℂ) + b * w‖ ^ 2 = (a + b * w.re) ^ 2 + (b * w.im) ^ 2`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hw, hn]`. Use polynomial arithmetic with `[sq_nonneg (a + b * w.re), sq_nonneg ((a + b * w.re) * w.re + b * w.im * w.im)]`.
-/
theorem normSq_lower (w : ℂ) (a b : ℝ) :
    (w.im) ^ 2 / (1 + ‖w‖ ^ 2) * (a ^ 2 + b ^ 2) ≤ ‖(a : ℂ) + b * w‖ ^ 2 := by
  have h1 : (0 : ℝ) < 1 + ‖w‖ ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ h1]
  have hw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hn : ‖(a : ℂ) + b * w‖ ^ 2 = (a + b * w.re) ^ 2 + (b * w.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [hw, hn]
  nlinarith [sq_nonneg (a + b * w.re), sq_nonneg ((a + b * w.re) * w.re + b * w.im * w.im)]

/- English proof (translation)
Introduce `F _ _ σ hσ z hz`. Use `set s := σ.re with hs`. Set `c : (F →+* ℝ) → ℝ` to `fun τ => 4 * Real.pi ^ 2 * ((z τ).im ^ 2 / (1 + ‖z τ‖ ^ 2))`. Establish `hc : ∀ τ, 0 < c τ` using `fun τ => by have := hz τ; positivity`. Use `⟨(∏ τ, c τ) ^ (-(1 + s)), fun p hp => ?_⟩` and prove the remaining obligations.

Use `set P := ∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2) with hPdef`. Establish `hP : 0 < P` using `Finset.prod_pos fun τ _ => by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h1 : τ p.1 = 0` using `by nlinarith [sq_nonneg (τ p.1), sq_nonneg (τ p.2)]`.

Establish `h2 : τ p.2 = 0` using `by nlinarith [sq_nonneg (τ p.1), sq_nonneg (τ p.2)]`. Conclude with `hp (Prod.ext ((map_eq_zero τ).1 h1) ((map_eq_zero τ).1 h2))`. Use `set N := ∏ τ, ‖latPt z p τ‖ with hN`. Establish `hNpos : 0 < N` using `Finset.prod_pos fun τ _ => norm_pos_iff.2 (latPt_ne_zero hz hp τ)`. Establish `hterm : ‖eisTerm 2 σ z p‖ = (N ^ 2) ^ (-(1 + s))`.

Unfold `eisTerm`. Simplify using `only [norm_mul, norm_pow, norm_inv, norm_prod]`. Rewrite using `[← hN, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]`. Rewrite using `[show (N ^ 2 : ℝ) = N ^ (2 : ℝ) from (Real.rpow_two N).symm, ← Real.rpow_mul hNpos.le]`. Establish `: (2 : ℝ) * (-(1 + s)) = -(2 : ℝ) + (-2 * σ).re` using `by simp [hs]; ring`.

Rewrite using `[this, Real.rpow_add hNpos, Real.rpow_neg hNpos.le, Real.rpow_two, inv_pow]`. Establish `hlow : (∏ τ, c τ) * P ≤ N ^ 2`. Rewrite using `[hPdef, hN, ← Finset.prod_mul_distrib, ← Finset.prod_pow]`. Use `Finset.prod_le_prod (fun τ _ => mul_nonneg (hc τ).le (by positivity)) fun τ _ => ?_` and prove the remaining obligations. Establish `hl : ‖latPt z p τ‖ ^ 2 = 4 * Real.pi ^ 2 * ‖((τ p.1 : ℝ) : ℂ) + (τ p.2 : ℝ) * z τ‖ ^ 2`.

Simplify using `only [latPt, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hl, mul_assoc (4 * Real.pi ^ 2)]`. Conclude with `mul_le_mul_of_nonneg_left (normSq_lower (z τ) _ _) (by positivity)`. Rewrite using `[hterm, ← Real.mul_rpow (Finset.prod_nonneg fun τ _ => (hc τ).le) hP.le]`.

Conclude with `Real.rpow_le_rpow_of_nonpos (mul_pos (Finset.prod_pos fun τ _ => hc τ) hP) hlow (by linarith)`.
-/
theorem bound : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∃ C : ℝ, ∀ p : F × F, p ≠ 0 → ‖GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm 2 σ z p‖ ≤ C * (∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2)) ^ (-(1 + σ.re)) := by
  intro F _ _ σ hσ z hz
  set s := σ.re with hs
  let c : (F →+* ℝ) → ℝ := fun τ => 4 * Real.pi ^ 2 * ((z τ).im ^ 2 / (1 + ‖z τ‖ ^ 2))
  have hc : ∀ τ, 0 < c τ := fun τ => by have := hz τ; positivity
  refine ⟨(∏ τ, c τ) ^ (-(1 + s)), fun p hp => ?_⟩
  set P := ∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2) with hPdef
  have hP : 0 < P := Finset.prod_pos fun τ _ => by
    by_contra h
    push_neg at h
    have h1 : τ p.1 = 0 := by nlinarith [sq_nonneg (τ p.1), sq_nonneg (τ p.2)]
    have h2 : τ p.2 = 0 := by nlinarith [sq_nonneg (τ p.1), sq_nonneg (τ p.2)]
    exact hp (Prod.ext ((map_eq_zero τ).1 h1) ((map_eq_zero τ).1 h2))
  set N := ∏ τ, ‖latPt z p τ‖ with hN
  have hNpos : 0 < N := Finset.prod_pos fun τ _ => norm_pos_iff.2 (latPt_ne_zero hz hp τ)
  have hterm : ‖eisTerm 2 σ z p‖ = (N ^ 2) ^ (-(1 + s)) := by
    unfold eisTerm
    simp only [norm_mul, norm_pow, norm_inv, norm_prod]
    rw [← hN, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    rw [show (N ^ 2 : ℝ) = N ^ (2 : ℝ) from (Real.rpow_two N).symm, ← Real.rpow_mul hNpos.le]
    have : (2 : ℝ) * (-(1 + s)) = -(2 : ℝ) + (-2 * σ).re := by simp [hs]; ring
    rw [this, Real.rpow_add hNpos, Real.rpow_neg hNpos.le, Real.rpow_two, inv_pow]
  have hlow : (∏ τ, c τ) * P ≤ N ^ 2 := by
    rw [hPdef, hN, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
    refine Finset.prod_le_prod (fun τ _ => mul_nonneg (hc τ).le (by positivity)) fun τ _ => ?_
    have hl : ‖latPt z p τ‖ ^ 2 = 4 * Real.pi ^ 2 * ‖((τ p.1 : ℝ) : ℂ) + (τ p.2 : ℝ) * z τ‖ ^ 2 := by
      simp only [latPt, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      ring
    rw [hl, mul_assoc (4 * Real.pi ^ 2)]
    exact mul_le_mul_of_nonneg_left (normSq_lower (z τ) _ _) (by positivity)
  rw [hterm, ← Real.mul_rpow (Finset.prod_nonneg fun τ _ => (hc τ).le) hP.le]
  exact Real.rpow_le_rpow_of_nonpos (mul_pos (Finset.prod_pos fun τ _ => hc τ) hP) hlow (by linarith)

end GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound
