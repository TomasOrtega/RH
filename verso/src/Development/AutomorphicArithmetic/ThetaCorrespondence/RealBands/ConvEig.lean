import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ _ N a f h s C hf hh`. Take `⟨hc, hb, hN, ha⟩` from `hh`. Establish `hbound : ∀ x g, ‖f g * h (g⁻¹ * x)‖ ≤ ‖f g‖ * C` using `fun x g => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)`.

Establish `hint : Integrable (fun g => ‖f g‖ * C) μ` using `hf.norm.mul_const C`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `conv`. Use `continuous_of_dominated (bound := fun g => ‖f g‖ * C) ?_ ?_ hint ?_` and prove the remaining obligations. Introduce `x`.

Use `hf.aestronglyMeasurable.mul ?_` and prove the remaining obligations. Conclude with `(hc.comp (continuous_inv.mul continuous_const)).aestronglyMeasurable`. Introduce `x`. Conclude with `Eventually.of_forall (hbound x)`. Use `Eventually.of_forall fun g => ?_` and prove the remaining obligations.

Conclude with `continuous_const.mul (hc.comp (continuous_const.mul continuous_id))`. Introduce `x`. Unfold `conv`. Rewrite using `[← integral_mul_const]`. Conclude with `norm_integral_le_of_norm_le hint (Eventually.of_forall (hbound x))`.

Introduce `x m hm`. Unfold `conv`. Simplify using `only [← mul_assoc, hN _ m hm]`. Introduce `x t`. Unfold `conv`.

Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[← mul_assoc, ha]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Lit.Cusp.conv_isEig :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (f h : G → ℂ) (s C : ℝ),
      Integrable f μ → IsEig N a s C h → IsEig N a s ((∫ g, ‖f g‖ ∂μ) * C) (conv μ f h) := by
  intro G _ _ _ _ _ _ _ _ μ _ N a f h s C hf hh
  obtain ⟨hc, hb, hN, ha⟩ := hh
  have hbound : ∀ x g, ‖f g * h (g⁻¹ * x)‖ ≤ ‖f g‖ * C := fun x g => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
  have hint : Integrable (fun g => ‖f g‖ * C) μ := hf.norm.mul_const C
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold conv
    refine continuous_of_dominated (bound := fun g => ‖f g‖ * C) ?_ ?_ hint ?_
    · intro x
      refine hf.aestronglyMeasurable.mul ?_
      exact (hc.comp (continuous_inv.mul continuous_const)).aestronglyMeasurable
    · intro x
      exact Eventually.of_forall (hbound x)
    · refine Eventually.of_forall fun g => ?_
      exact continuous_const.mul (hc.comp (continuous_const.mul continuous_id))
  · intro x
    unfold conv
    rw [← integral_mul_const]
    exact norm_integral_le_of_norm_le hint (Eventually.of_forall (hbound x))
  · intro x m hm
    unfold conv
    simp only [← mul_assoc, hN _ m hm]
  · intro x t
    unfold conv
    rw [← integral_const_mul]
    congr 1
    funext g
    rw [← mul_assoc, ha]
    ring
