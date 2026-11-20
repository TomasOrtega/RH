import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace RestCutLieFirst

/- English proof (translation)
Rewrite using `[Finset.mul_sum]`. Simplify using `only [RestTerms.smallPowerSum, map_sum, map_pow]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `hidx : (restFirstEquiv j k) (⟨a.val, by omega⟩ : Fin (j + k)) = Sum.inl a`. Establish `: (⟨a.val, by omega⟩ : Fin (j + k)) = Fin.castAdd k a` using `rfl`.

Rewrite using `[this, restFirstEquiv, finSumFinEquiv_symm_apply_castAdd]`. Simplify using `only [RestTerms.yRoot, RestTerms.yIndex, RestTerms.SmallBlock.sign, restTransport, restRename, RingHom.comp_apply, map_mul, map_C, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, rename_C, hidx]`. Rewrite using `[mul_pow]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem transport_smallPowerSum (f j k m : ℕ) (τ : Fin f) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.smallPowerSum f j k .first m τ) =
      (-1) ^ m * ∑ a : Fin j, (X (τ, Sum.inl a) : RootPoly f j k) ^ m := by
  rw [Finset.mul_sum]
  simp only [RestTerms.smallPowerSum, map_sum, map_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hidx : (restFirstEquiv j k) (⟨a.val, by omega⟩ : Fin (j + k)) = Sum.inl a := by
    have : (⟨a.val, by omega⟩ : Fin (j + k)) = Fin.castAdd k a := rfl
    rw [this, restFirstEquiv, finSumFinEquiv_symm_apply_castAdd]
  simp only [RestTerms.yRoot, RestTerms.yIndex, RestTerms.SmallBlock.sign, restTransport,
    restRename, RingHom.comp_apply, map_mul, map_C, map_X, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, rename_X, rename_C, hidx]
  rw [mul_pow]
  congr 1
  simp

end RestCutLieFirst

/- English proof (translation)
Introduce `f j k _ m σ`. Take `⟨τ, b⟩` from `σ`. Establish `hC1 : (C ((((-1 : ℚ) ^ m : ℚ) : ℝ)) : RootPoly f j k) = (-1) ^ m` using `by simp`. Establish `hC2 : (C (((-1 : ℚ) : ℚ) : ℝ) : RootPoly f j k) = -1` using `by simp`. Establish `hC3 : (C ((-1 : ℝ) ^ m) : RootPoly f j k) = (-1) ^ m` using `by simp`.

Consider the cases of `b with`. Consider the case `false`. Use `⟨(-1) ^ m, 0, neg_one_pow_eq_or ℚ m, ?_⟩` and prove the remaining obligations. Rewrite using `[RestCutLieFirst.transport_smallPowerSum, hC1]`. Simplify using `only [lieClass, map_zero, zero_mul, add_zero]`.

Rewrite using `[← mul_assoc, ← mul_pow]`. Simplify using the standard rewrite rules. Consider the case `true`. Use `⟨-1, (-1) ^ m, Or.inr rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[RestCutLieFirst.transport_smallPowerSum, hC2, hC3]`.

Simplify using `only [lieClass, rootPsum, Fintype.sum_sum_type]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem RestCutLieFirst.proof : RestCutLieFirst.Statement := by
  intro f j k _ m σ
  obtain ⟨τ, b⟩ := σ
  have hC1 : (C ((((-1 : ℚ) ^ m : ℚ) : ℝ)) : RootPoly f j k) = (-1) ^ m := by simp
  have hC2 : (C (((-1 : ℚ) : ℚ) : ℝ) : RootPoly f j k) = -1 := by simp
  have hC3 : (C ((-1 : ℝ) ^ m) : RootPoly f j k) = (-1) ^ m := by simp
  cases b with
  | false =>
    refine ⟨(-1) ^ m, 0, neg_one_pow_eq_or ℚ m, ?_⟩
    rw [RestCutLieFirst.transport_smallPowerSum, hC1]
    simp only [lieClass, map_zero, zero_mul, add_zero]
    rw [← mul_assoc, ← mul_pow]
    simp
  | true =>
    refine ⟨-1, (-1) ^ m, Or.inr rfl, ?_⟩
    rw [RestCutLieFirst.transport_smallPowerSum, hC2, hC3]
    simp only [lieClass, rootPsum, Fintype.sum_sum_type]
    ring

end

end GroundTheory.Heights₂.Heights
