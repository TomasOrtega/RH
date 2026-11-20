import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepNeZero
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.Div.LipschitzCone

/- English proof (translation)
Rewrite using `[sign_mul, sign_pos hw, mul_one]`. Break down `lt_or_gt_of_ne hx with h | h` into its components or cases. Rewrite using `[sign_neg h]`. Simplify using `only [SignType.coe_neg, SignType.coe_one, neg_mul, one_mul, Left.neg_pos_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Conclude with `mul_pos_of_neg_of_neg hy h`. Introduce `hyx`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Use `mul_nonpos_of_nonneg_of_nonpos hc h.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[sign_pos h]`. Simplify using `only [SignType.coe_one, one_mul]`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Conclude with `mul_pos hy h`. Introduce `hyx`. Conclude with `pos_of_mul_pos_left hyx h.le`.
-/
theorem sign_cone_iff (x y w : ℝ) (hx : x ≠ 0) (hw : 0 < w) :
    0 < (SignType.sign (x * w) : ℝ) * y ↔ 0 < y * x := by
  rw [sign_mul, sign_pos hw, mul_one]
  rcases lt_or_gt_of_ne hx with h | h
  · rw [sign_neg h]
    simp only [SignType.coe_neg, SignType.coe_one, neg_mul, one_mul, Left.neg_pos_iff]
    constructor
    · intro hy; exact mul_pos_of_neg_of_neg hy h
    · intro hyx
      by_contra hc
      push_neg at hc
      have := mul_nonpos_of_nonneg_of_nonpos hc h.le
      linarith
  · rw [sign_pos h]
    simp only [SignType.coe_one, one_mul]
    constructor
    · intro hy; exact mul_pos hy h
    · intro hyx; exact pos_of_mul_pos_left hyx h.le

/- English proof (translation)
Introduce `F _ _ 𝔞 b hb z hz ν`. Establish `ha : (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0` using `𝔞.ne_zero`. Establish `hM : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 ≠ 0`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual]`. Conclude with `FractionalIdeal.dual_ne_zero ℤ ℚ ha`.

Unfold `GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.dualCone`. Simplify using `only [Set.mem_setOf_eq]`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.mem_traceDual_iff hM, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, FractionalIdeal.dual_dual]`. Use `and_congr Iff.rfl (forall_congr' fun τ => ?_)` and prove the remaining obligations. Rewrite using `[Complex.im_ofReal_mul, map_mul τ ν b]`.

Conclude with `sign_cone_iff _ _ _ ((map_ne_zero τ).2 hb) (hz τ)`.
-/
theorem cone_iff : ∀ (F : Type) [Field F] [NumberField F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (b : F), b ≠ 0 →
    ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ ν : F,
      ν ∈ GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.dualCone (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞) (fun τ => ((τ b : ℝ) : ℂ) * z τ) ↔
        (ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ τ : F →+* ℝ, 0 < τ (ν * b)) := by
  intro F _ _ 𝔞 b hb z hz ν
  have ha : (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := 𝔞.ne_zero
  have hM : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 ≠ 0 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual]
    exact FractionalIdeal.dual_ne_zero ℤ ℚ ha
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.dualCone
  simp only [Set.mem_setOf_eq]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.mem_traceDual_iff hM, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, FractionalIdeal.dual_dual]
  refine and_congr Iff.rfl (forall_congr' fun τ => ?_)
  rw [Complex.im_ofReal_mul, map_mul τ ν b]
  exact sign_cone_iff _ _ _ ((map_ne_zero τ).2 hb) (hz τ)

end GlobalTheory.Div.LipschitzCone
