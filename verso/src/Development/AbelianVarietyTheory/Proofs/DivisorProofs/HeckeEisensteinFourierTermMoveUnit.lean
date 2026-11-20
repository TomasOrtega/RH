import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqProd
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwoUnit

/- English proof (translation)
Unfold `phi`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (abs_nonneg l) (norm_nonneg w), mul_inv, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phi_smul (σ : ℂ) {l : ℝ} (hl : l ≠ 0) (w : ℂ) :
    phi σ ((l : ℂ) * w) = ((l : ℂ)⁻¹ ^ 2 * ((|l| : ℝ) : ℂ) ^ (-2 * σ)) * phi σ w := by
  unfold phi
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (abs_nonneg l) (norm_nonneg w), mul_inv, mul_pow]
  ring

/- English proof (translation)
Establish `h1 : ((|l| : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast abs_ne_zero.2 hl`. Establish `h2 : (l : ℂ) ^ 2 = ((|l| : ℝ) : ℂ) ^ 2`. Rewrite using `[← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]`. Rewrite using `[inv_pow, h2]`. Clear the denominators using the available nonvanishing facts.
-/
theorem abs_mul_inv_sq {l : ℝ} (hl : l ≠ 0) :
    ((|l| : ℝ) : ℂ) * (l : ℂ)⁻¹ ^ 2 = ((|l| : ℝ) : ℂ)⁻¹ := by
  have h1 : ((|l| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.2 hl
  have h2 : (l : ℂ) ^ 2 = ((|l| : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
  rw [inv_pow, h2]; field_simp

/- English proof (translation)
Establish `key` using `MeasureTheory.Measure.integral_comp_mul_left (fun t : ℝ => phi σ ((t : ℂ) + ((l * y : ℝ) : ℂ) * I) * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))) l`. Unfold `hTrans`. Rewrite using `[← smul_eq_mul (a := ((|l| : ℝ) : ℂ) ^ _)]`. Establish `habs : |l⁻¹| = |l|⁻¹` using `abs_inv l`. Establish `hpos : 0 < |l|` using `abs_pos.2 hl`.

Establish `e1 : ∫ t : ℝ, phi σ ((t : ℂ) + ((l * y : ℝ) : ℂ) * I) * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))) = |l| • ∫ t : ℝ, phi σ (((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I) * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * ((l * t : ℝ) : ℂ)))`. Rewrite using `[key, habs, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]`. Rewrite using `[e1]`. Establish `e2 : ∀ t : ℝ, phi σ (((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I) * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * ((l * t : ℝ) : ℂ))) = ((l : ℂ)⁻¹ ^ 2 * ((|l| : ℝ) : ℂ) ^ (-2 * σ)) * (phi σ ((t : ℂ) + (y : ℂ) * I) * Complex.exp (-(2 * (Real.pi : ℂ) * I * ((l * ν : ℝ) : ℂ) * (t : …`. Introduce `t`.

Rewrite using `[show ((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I = (l : ℂ) * ((t : ℂ) + (y : ℂ) * I) by push_cast; ring, phi_smul σ hl]`. Use `push_cast`. Put the polynomial expressions in normal form. Repeatedly rewrite using `[e2]`. Rewrite using `[MeasureTheory.integral_const_mul, Complex.real_smul, smul_eq_mul, ← mul_assoc, ← mul_assoc, abs_mul_inv_sq hl]`.

Use `congr 1`. Establish `h1 : ((|l| : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hpos.ne'`. Rewrite using `[sub_eq_add_neg, Complex.cpow_add _ _ h1, Complex.cpow_neg_one, neg_mul]`.
-/
theorem hTrans_smul (σ : ℂ) {l : ℝ} (hl : l ≠ 0) (ν y : ℝ) :
    hTrans σ ν (l * y) = ((|l| : ℝ) : ℂ) ^ (-1 - 2 * σ) * hTrans σ (l * ν) y := by
  have key := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => phi σ ((t : ℂ) + ((l * y : ℝ) : ℂ) * I) *
      Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))) l
  unfold hTrans
  rw [← smul_eq_mul (a := ((|l| : ℝ) : ℂ) ^ _)]
  have habs : |l⁻¹| = |l|⁻¹ := abs_inv l
  have hpos : 0 < |l| := abs_pos.2 hl
  have e1 : ∫ t : ℝ, phi σ ((t : ℂ) + ((l * y : ℝ) : ℂ) * I) *
      Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))) =
      |l| • ∫ t : ℝ, phi σ (((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * ((l * t : ℝ) : ℂ))) := by
    rw [key, habs, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  rw [e1]
  have e2 : ∀ t : ℝ, phi σ (((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * ((l * t : ℝ) : ℂ))) =
      ((l : ℂ)⁻¹ ^ 2 * ((|l| : ℝ) : ℂ) ^ (-2 * σ)) * (phi σ ((t : ℂ) + (y : ℂ) * I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * I * ((l * ν : ℝ) : ℂ) * (t : ℂ)))) := by
    intro t
    rw [show ((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I = (l : ℂ) * ((t : ℂ) + (y : ℂ) * I) by push_cast; ring,
      phi_smul σ hl]
    push_cast; ring_nf
  simp_rw [e2]
  rw [MeasureTheory.integral_const_mul, Complex.real_smul, smul_eq_mul, ← mul_assoc, ← mul_assoc,
    abs_mul_inv_sq hl]
  congr 1
  have h1 : ((|l| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [sub_eq_add_neg, Complex.cpow_add _ _ h1, Complex.cpow_neg_one, neg_mul]

end GlobalTheory.HeckeTwoUnit

namespace GlobalTheory.HeckeTwoUnit

/- English proof (translation)
Establish `hprod : ∀ (S : Finset (Emb F)), ∏ τ ∈ S, ((|τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ s = ((∏ τ ∈ S, |τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ s` using `by classical`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a S ha ih`.

Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (Finset.prod_nonneg fun _ _ => abs_nonneg _)]`. Rewrite using `[hprod]`. Establish `h` using `GlobalTheory.HeckeTwoExp.abs_norm_eq_prod ((ε : 𝓞 F) : F)`. Rewrite `h` using `[← Complex.ofReal_prod]`. Establish `hn : |((Algebra.norm ℚ ((ε : 𝓞 F) : F) : ℚ) : ℝ)| = 1`.

Use `Units.norm F ε` as an intermediate fact. Conclude with `this` after adjusting the coercions. Rewrite using `[← h, hn, Complex.ofReal_one, Complex.one_cpow]`.
-/
theorem prod_abs_unit_cpow {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (ε : (𝓞 F)ˣ) (s : ℂ) :
    ∏ τ : Emb F, ((|τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ s = 1 := by
  have hprod : ∀ (S : Finset (Emb F)), ∏ τ ∈ S, ((|τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ s =
      ((∏ τ ∈ S, |τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ s := by
    classical
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (Finset.prod_nonneg fun _ _ => abs_nonneg _)]
  rw [hprod]
  have h := GlobalTheory.HeckeTwoExp.abs_norm_eq_prod ((ε : 𝓞 F) : F)
  rw [← Complex.ofReal_prod] at h
  have hn : |((Algebra.norm ℚ ((ε : 𝓞 F) : F) : ℚ) : ℝ)| = 1 := by
    have := Units.norm F ε
    exact_mod_cast this
  rw [← h, hn, Complex.ofReal_one, Complex.one_cpow]

/- English proof (translation)
Establish `hne : ∀ τ : Emb F, τ ((ε : 𝓞 F) : F) ≠ 0` using `fun τ h => by`. Establish `hu : ((ε : 𝓞 F) : F) ≠ 0`. Introduce `h0`. Use `unit_inv_mul ε` as an intermediate fact. Rewrite `this` using `[h0, mul_zero]`.

Conclude with `zero_ne_one this`. Conclude with `hu ((map_eq_zero τ).1 h)`. Unfold `fTerm`. Establish `e : ∀ τ : Emb F, Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ (((ε : 𝓞 F) : F) * b) * (z τ).re : ℝ) : ℂ)) * hTrans σ (τ ν) (τ (((ε : 𝓞 F) : F) * b) * (z τ).im) = ((|τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ (-1 - 2 * σ) * (Complex.exp (2 * (Real.pi : ℂ) * I * ((τ (((ε : 𝓞 F) : F) * ν) * τ …`. Introduce `τ`.

Rewrite using `[map_mul, map_mul, mul_assoc (τ ((ε : 𝓞 F) : F)) (τ b), hTrans_smul σ (hne τ)]`. Rewrite using `[show τ ν * (τ ((ε : 𝓞 F) : F) * τ b) * (z τ).re = τ ((ε : 𝓞 F) : F) * τ ν * τ b * (z τ).re by ring]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e]`. Rewrite using `[Finset.prod_mul_distrib, prod_abs_unit_cpow, one_mul]`.
-/
theorem fTerm_unit_mul {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (σ : ℂ) (z : Emb F → ℂ) (b ν : F)
    (ε : (𝓞 F)ˣ) :
    fTerm σ z (((ε : 𝓞 F) : F) * b) ν = fTerm σ z b (((ε : 𝓞 F) : F) * ν) := by
  have hne : ∀ τ : Emb F, τ ((ε : 𝓞 F) : F) ≠ 0 := fun τ h => by
    have hu : ((ε : 𝓞 F) : F) ≠ 0 := by
      intro h0; have := unit_inv_mul ε; rw [h0, mul_zero] at this; exact zero_ne_one this
    exact hu ((map_eq_zero τ).1 h)
  unfold fTerm
  have e : ∀ τ : Emb F, Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ (((ε : 𝓞 F) : F) * b) * (z τ).re : ℝ) : ℂ)) *
      hTrans σ (τ ν) (τ (((ε : 𝓞 F) : F) * b) * (z τ).im) =
      ((|τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ (-1 - 2 * σ) *
      (Complex.exp (2 * (Real.pi : ℂ) * I * ((τ (((ε : 𝓞 F) : F) * ν) * τ b * (z τ).re : ℝ) : ℂ)) *
      hTrans σ (τ (((ε : 𝓞 F) : F) * ν)) (τ b * (z τ).im)) := by
    intro τ
    rw [map_mul, map_mul, mul_assoc (τ ((ε : 𝓞 F) : F)) (τ b), hTrans_smul σ (hne τ)]
    rw [show τ ν * (τ ((ε : 𝓞 F) : F) * τ b) * (z τ).re = τ ((ε : 𝓞 F) : F) * τ ν * τ b * (z τ).re by ring]
    ring
  simp_rw [e]
  rw [Finset.prod_mul_distrib, prod_abs_unit_cpow, one_mul]

end GlobalTheory.HeckeTwoUnit

namespace GlobalTheory.HeckeTwoUnit

/- English proof (translation)
Introduce `_ _ _ _ σ z b ν ε` and use `fTerm_unit_mul σ z b ν ε`.
-/
theorem fTerm_unit_move : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (σ : ℂ) (z : Emb F → ℂ) (b ν : F) (ε : (𝓞 F)ˣ),
    fTerm σ z (((ε : 𝓞 F) : F) * b) ν = fTerm σ z b (((ε : 𝓞 F) : F) * ν) :=
  fun _ _ _ _ σ z b ν ε => fTerm_unit_mul σ z b ν ε

end GlobalTheory.HeckeTwoUnit
