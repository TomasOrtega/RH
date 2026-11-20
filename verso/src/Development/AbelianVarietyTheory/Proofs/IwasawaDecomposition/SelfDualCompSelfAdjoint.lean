import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

/- English proof (translation)
Introduce `V _ _ _ _ _ _ _ _ μ χ T δ hδ hμ hχ hsd`. Establish `hH` using `hsd.1`. Establish `hs0 : NNReal.sqrt δ ≠ 0` using `by simpa using hδ`. Use `⟨Measure.IsAddHaarMeasure.nnreal_smul μ hs0, ?_⟩` and prove the remaining obligations. Introduce `Φ hc hcs hI z`.

Use `set s : ℝ≥0 := NNReal.sqrt δ with hs`. Use `set F : V → ℂ := fun y => ∫ x, Φ x * χ x y ∂μ with hF`. Establish `hT : ∀ y, ∫ x, Φ x * χ x (T y) ∂(s • μ) = (s : ℂ) * F (T y)`. Introduce `y`. Rewrite using `[integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]`.

Establish `hsC : (s : ℂ) ≠ 0` using `by exact_mod_cast hs0`. Establish `hmap : μ.map T = μ.map T.toMeasurableEquiv` using `rfl`. Simplify using `only [hT] at hI ⊢`. Establish `h1 : Integrable (fun y => F (T y)) μ`. Establish `h2 : Integrable (fun y => (s : ℂ) * F (T y)) μ`.

Use `hI.smul_measure_nnreal (c := s⁻¹)` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hs0, one_smul]`. Then use the resulting hypothesis. Use `h2.const_mul ((s : ℂ)⁻¹)` as an intermediate fact. Simplify `this` using `[← mul_assoc, inv_mul_cancel₀ hsC]`. Establish `h3 : Integrable F μ`.

Rewrite using `[hμ]`. Apply `Integrable.smul_measure_nnreal` to reduce the goal to its premises. Rewrite using `[hmap, integrable_map_equiv]`. Conclude with `h1`. Establish `h4` using `hsd.2 Φ hc hcs h3 z`.

Rewrite using `[← h4]`. Establish `h5 : ∫ y, F y * χ y z ∂μ = (δ : ℂ) * ∫ y, F (T y) * χ (T y) z ∂μ` using `by conv_lhs => rw [hμ]`. Rewrite using `[integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, hmap, integral_map_equiv]`. Both sides reduce to the same expression. Establish `hss : (s : ℂ) * (s : ℂ) = (δ : ℂ)`.

Establish `: s * s = δ` using `NNReal.mul_self_sqrt δ`. Rewrite using `[← this]`. Use `push_cast`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `_ = ∫ y, F y * χ y z ∂μ`.

Rewrite using `[h5, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, ← hss, mul_assoc]`. Use `congr 1`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use extensionality with `y`.

Rewrite using `[hχ, mul_assoc]`.
-/
theorem selfDual_comp_selfAdjoint : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (χ : V → V → ℂ) (T : V ≃ₜ V) (δ : ℝ≥0), δ ≠ 0 → μ = δ • μ.map T → (∀ x y, χ x (T y) = χ (T x) y) → SelfDual μ χ → SelfDual (NNReal.sqrt δ • μ) (fun x y => χ x (T y)) := by
  intro V _ _ _ _ _ _ _ _ μ χ T δ hδ hμ hχ hsd
  have hH := hsd.1
  have hs0 : NNReal.sqrt δ ≠ 0 := by simpa using hδ
  refine ⟨Measure.IsAddHaarMeasure.nnreal_smul μ hs0, ?_⟩
  intro Φ hc hcs hI z
  set s : ℝ≥0 := NNReal.sqrt δ with hs
  set F : V → ℂ := fun y => ∫ x, Φ x * χ x y ∂μ with hF
  have hT : ∀ y, ∫ x, Φ x * χ x (T y) ∂(s • μ) = (s : ℂ) * F (T y) := by
    intro y
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hmap : μ.map T = μ.map T.toMeasurableEquiv := rfl
  simp only [hT] at hI ⊢
  have h1 : Integrable (fun y => F (T y)) μ := by
    have h2 : Integrable (fun y => (s : ℂ) * F (T y)) μ := by
      have := hI.smul_measure_nnreal (c := s⁻¹)
      rwa [smul_smul, inv_mul_cancel₀ hs0, one_smul] at this
    have := h2.const_mul ((s : ℂ)⁻¹)
    simpa [← mul_assoc, inv_mul_cancel₀ hsC] using this
  have h3 : Integrable F μ := by
    rw [hμ]
    apply Integrable.smul_measure_nnreal
    rw [hmap, integrable_map_equiv]
    exact h1
  have h4 := hsd.2 Φ hc hcs h3 z
  rw [← h4]
  have h5 : ∫ y, F y * χ y z ∂μ = (δ : ℂ) * ∫ y, F (T y) * χ (T y) z ∂μ := by
    conv_lhs => rw [hμ]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, hmap, integral_map_equiv]
    rfl
  have hss : (s : ℂ) * (s : ℂ) = (δ : ℂ) := by
    have : s * s = δ := NNReal.mul_self_sqrt δ
    rw [← this]; push_cast; rfl
  change _ = ∫ y, F y * χ y z ∂μ
  rw [h5, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, ← hss, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  congr 1
  ext y
  rw [hχ, mul_assoc]

end GlobalTheory.GaugeEx
