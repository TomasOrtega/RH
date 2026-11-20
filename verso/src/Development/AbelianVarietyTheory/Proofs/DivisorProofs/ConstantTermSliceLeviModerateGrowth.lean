import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermModerateGrowth
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.LeviGA

namespace GlobalTheory.SliceTwo.Growth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

omit [IsTotallyComplex E] in

/- English proof (translation)
Unfold `height`. Rewrite using `[inv_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem height_inv {a : ℕ} (y : GL (Fin a) (Cinf E)) : height y⁻¹ = height y := by
  unfold height; rw [inv_inv]; ring

omit [IsTotallyComplex E] in

/- English proof (translation)
Take `⟨B, hB, h⟩` from `GlobalTheory.ConstTermGrowth.height_mul_left_le (E := E) (isCompact_singleton (x := c⁻¹))`. Use `⟨B, hB, fun y => ?_⟩` and prove the remaining obligations. Use `h _ rfl y⁻¹` as an intermediate fact. Rewrite `this` using `[← _root_.mul_inv_rev, height_inv, height_inv]`. Then use the resulting hypothesis.
-/
theorem height_mul_right_le {a : ℕ} (c : GL (Fin a) (Cinf E)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, height (y * c) ≤ B * height y := by
  obtain ⟨B, hB, h⟩ := GlobalTheory.ConstTermGrowth.height_mul_left_le (E := E) (isCompact_singleton (x := c⁻¹))
  refine ⟨B, hB, fun y => ?_⟩
  have := h _ rfl y⁻¹
  rwa [← _root_.mul_inv_rev, height_inv, height_inv] at this

omit [IsTotallyComplex E] in

/- English proof (translation)
Establish `h0 : (0 : ℝ) ≤ 1 + ‖toL y.val‖` using `by positivity`. Use `(pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_` and prove the remaining obligations. Take `⟨i, rfl⟩` from `(blkEquiv hr).surjective i`. Take `⟨j, rfl⟩` from `(blkEquiv hr).surjective j`. Express the relevant statement in the definitionally equal form `‖(blkGL hr (1, y) : Matrix (Fin a) (Fin a) (Cinf E)) (blkEquiv hr i) (blkEquiv hr j)‖ ≤ _`.

Rewrite using `[blkGL_apply]`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`. Simplify using `only [Matrix.fromBlocks_apply₁₁, Units.val_one]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Rewrite using `[Matrix.one_apply_eq]`. Use `((pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => ?_).trans (by linarith [norm_nonneg (toL y.val)])` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne hij, norm_zero]`. Conclude with `h0`.

Simplify using `only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, norm_zero]`. Conclude with `h0`. Simplify using `only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, norm_zero]`. Conclude with `h0`. Simplify using `only [Matrix.fromBlocks_apply₂₂]`.

Conclude with `((norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i)).trans (by linarith)`.
-/
theorem norm_toL_blkGL_one_le {a r : ℕ} (hr : r ≤ a) (y : GL (Fin (a - r)) (Cinf E)) :
    ‖toL (blkGL hr (1, y)).val‖ ≤ 1 + ‖toL y.val‖ := by
  have h0 : (0 : ℝ) ≤ 1 + ‖toL y.val‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  obtain ⟨i, rfl⟩ := (blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv hr).surjective j
  change ‖(blkGL hr (1, y) : Matrix (Fin a) (Fin a) (Cinf E)) (blkEquiv hr i) (blkEquiv hr j)‖ ≤ _
  rw [blkGL_apply]
  rcases i with i | i <;> rcases j with j | j
  · simp only [Matrix.fromBlocks_apply₁₁, Units.val_one]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq]
      refine ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => ?_).trans (by linarith [norm_nonneg (toL y.val)])
      simp
    · rw [Matrix.one_apply_ne hij, norm_zero]; exact h0
  · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, norm_zero]; exact h0
  · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, norm_zero]; exact h0
  · simp only [Matrix.fromBlocks_apply₂₂]
    exact ((norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i)).trans
      (by linarith)

omit [IsTotallyComplex E] in

/- English proof (translation)
Establish `e : (blkGL hr (1, y))⁻¹ = blkGL hr (1, y⁻¹)`. Rewrite using `[← map_inv, Prod.inv_mk, inv_one]`. Establish `h1` using `norm_toL_blkGL_one_le hr y`. Establish `h2` using `norm_toL_blkGL_one_le hr y⁻¹`. Establish `n1` using `norm_nonneg (toL y.val)`.

Establish `n2` using `norm_nonneg (toL (y⁻¹).val)`. Unfold `height`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem height_blkGL_one_le {a r : ℕ} (hr : r ≤ a) (y : GL (Fin (a - r)) (Cinf E)) :
    height (blkGL hr (1, y)) ≤ 3 * height y := by
  have e : (blkGL hr (1, y))⁻¹ = blkGL hr (1, y⁻¹) := by
    rw [← map_inv, Prod.inv_mk, inv_one]
  have h1 := norm_toL_blkGL_one_le hr y
  have h2 := norm_toL_blkGL_one_le hr y⁻¹
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  unfold height
  rw [e]
  linarith

end GlobalTheory.SliceTwo.Growth

open GlobalTheory.SliceTwo.Growth in

/- English proof (translation)
Introduce `E _ _ _ a r hr _ _ μ 𝓕 hμ hF h1 φ hφ m₁ t κ g`. Take `⟨C, N, hC⟩` from `GlobalTheory.ConstTermGrowth.norm_constTerm_le E a r μ 𝓕 hμ hF h1 φ hφ.left hφ.level hφ.growth (blkGL hr (m₁, g) * finGL E a t)`. Take `⟨B, hB0, hB⟩` from `height_mul_right_le (E := E) (Unitary.toUnits κ)`. Use `⟨|C| * (3 * B) ^ N, N, fun y => ?_⟩` and prove the remaining obligations. Establish `e : GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) y) = ∫ x in 𝓕, φ.1 (unip x * ((blkGL hr (m₁, g) * finGL E a t) * infGL E a (blkGL hr (1, y) * Unitary.toUnits κ))) ∂μ`.

Unfold `GlobalTheory.SliceTwo.slice`. Use `congr 1`. Use function extensionality and compare the values at `x`. Use `congr 2`. Rewrite using `[GlobalTheory.SliceTwo.blkGL_mul_infGL, map_mul]`.

Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc (infGL E a (blkGL hr (1, y))) (finGL E a t), infGL_comm]`. Simplify using `only [mul_assoc]`. Rewrite using `[e]`. Use `(hC _).trans ?_` and prove the remaining obligations.

Establish `hy` using `one_le_height y`. Establish `hb` using `one_le_height (blkGL hr (1, y) * Unitary.toUnits κ)`. Establish `h3 : height (blkGL hr (1, y) * Unitary.toUnits κ) ≤ 3 * B * height y`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem GlobalTheory.SliceTwo.Growth.norm_slice_le : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ)
    (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, IsAutForm φ →
    ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (g : GA E (a - r)), ∃ (C : ℝ) (M : ℕ), ∀ y,
      ‖GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) y)‖ ≤ C * height y ^ M := by
  intro E _ _ _ a r hr _ _ μ 𝓕 hμ hF h1 φ hφ m₁ t κ g
  obtain ⟨C, N, hC⟩ := GlobalTheory.ConstTermGrowth.norm_constTerm_le E a r μ 𝓕 hμ hF h1 φ hφ.left hφ.level hφ.growth
    (blkGL hr (m₁, g) * finGL E a t)
  obtain ⟨B, hB0, hB⟩ := height_mul_right_le (E := E) (Unitary.toUnits κ)
  refine ⟨|C| * (3 * B) ^ N, N, fun y => ?_⟩
  have e : GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) y) =
      ∫ x in 𝓕, φ.1 (unip x * ((blkGL hr (m₁, g) * finGL E a t) *
        infGL E a (blkGL hr (1, y) * Unitary.toUnits κ))) ∂μ := by
    unfold GlobalTheory.SliceTwo.slice
    congr 1
    funext x
    congr 2
    rw [GlobalTheory.SliceTwo.blkGL_mul_infGL, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (infGL E a (blkGL hr (1, y))) (finGL E a t), infGL_comm]
    simp only [mul_assoc]
  rw [e]
  refine (hC _).trans ?_
  have hy := one_le_height y
  have hb := one_le_height (blkGL hr (1, y) * Unitary.toUnits κ)
  have h3 : height (blkGL hr (1, y) * Unitary.toUnits κ) ≤ 3 * B * height y := by
    calc _ ≤ B * height (blkGL hr (1, y)) := hB _
      _ ≤ B * (3 * height y) := mul_le_mul_of_nonneg_left (height_blkGL_one_le hr y) hB0
      _ = 3 * B * height y := by ring
  calc C * height (blkGL hr (1, y) * Unitary.toUnits κ) ^ N
      ≤ |C| * height (blkGL hr (1, y) * Unitary.toUnits κ) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith) _)
    _ ≤ |C| * (3 * B * height y) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h3 _) (abs_nonneg C)
    _ = |C| * (3 * B) ^ N * height y ^ N := by ring

end
