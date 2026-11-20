import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeas
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ConeHaar

/- English proof (translation)
Introduce `Γ K X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he _ ρ _ s hs hρ hinv hfin μ _`. Choose the witnesses or unpack the hypotheses as in `⟨m, hmH, hm1⟩ : ∃ m : Measure K, m.IsHaarMeasure ∧ m Set.univ = 1 := by`. Use `⟨Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K), inferInstance, ?_⟩` and prove the remaining obligations. Establish `h` using `Measure.haarMeasure_self (G := K) (K₀ := ⊤)`. Rewrite `h` using `[TopologicalSpace.PositiveCompacts.coe_top]`. Then use the resulting hypothesis.

Use `haveI := hmH`. Use `haveI : IsFiniteMeasure m := ⟨by rw [hm1]; exact ENNReal.one_lt_top⟩`. Use `set φ : X × K → Γ := fun p => s p.1 * e p.2 with hφ_def`. Establish `hφ : Measurable φ` using `(hs.comp measurable_fst).mul (he.measurable.comp measurable_snd)`. Use `set ν : Measure Γ := Measure.map φ (ρ.prod m) with hν_def`.

Establish `key : ∀ (B : Set Γ) (y : Γ) (k : K), m ((fun k' => y * e k * e k') ⁻¹' B) = m ((fun k' => y * e k') ⁻¹' B)`. Introduce `B y k`. Establish `h : (fun k' => y * e k * e k') ⁻¹' B = (fun k' => k * k') ⁻¹' ((fun k' => y * e k') ⁻¹' B)`. Use extensionality with `k'`. Simplify using `[map_mul, mul_assoc]`.

Rewrite using `[h, measure_preimage_mul]`. Establish `hνapp : ∀ B : Set Γ, MeasurableSet B → ν B = ∫⁻ x, m ((fun k => s x * e k) ⁻¹' B) ∂ρ`. Introduce `B hB`. Rewrite using `[hν_def, Measure.map_apply hφ hB, Measure.prod_apply (hφ hB)]`. Both sides reduce to the same expression.

Establish `hmeasψ : ∀ B : Set Γ, MeasurableSet B → Measurable (fun x => m ((fun k => s x * e k) ⁻¹' B))`. Introduce `B hB`. Conclude with `measurable_measure_prodMk_left (hφ hB)`. Use `haveI : ν.IsMulLeftInvariant := by`. Prove the components needed by the constructor for the conclusion.

Introduce `g`. Use extensionality with `B hB`. Rewrite using `[Measure.map_apply (measurable_const_mul g) hB, hνapp _ (measurable_const_mul g hB), hνapp B hB]`. Take `⟨a, ha, hamap, hae⟩` from `hinv g`. Combine the equalities or inequalities in the displayed calculation.

Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with x hx`. Take `⟨k, hk⟩` from `hx`. Establish `h1 : (fun k' => s x * e k') ⁻¹' ((fun h => g * h) ⁻¹' B) = (fun k' => s (a x) * e k * e k') ⁻¹' B`. Use extensionality with `k'`.

Simplify using `only [Set.mem_preimage]`. Rewrite using `[← mul_assoc, hk]`. Rewrite using `[h1, key]`. Use `_ = ∫⁻ y, m ((fun k => s y * e k) ⁻¹' B) ∂(Measure.map a ρ) := by`. Rewrite using `[lintegral_map (hmeasψ B hB) ha]`.

Use `_ = ∫⁻ y, m ((fun k => s y * e k) ⁻¹' B) ∂ρ := by rw [hamap]`. Use `haveI : IsFiniteMeasureOnCompacts ν := by`. Prove the components needed by the constructor for the conclusion. Introduce `A hA`. Establish `hsub : φ ⁻¹' A ⊆ (s ⁻¹' (A * Set.range e)) ×ˢ Set.univ`.

Introduce `p hp`. Use `⟨?_, Set.mem_univ _⟩` and prove the remaining obligations. Simplify using `only [Set.mem_preimage] at hp ⊢`. Conclude with `Set.mem_mul.mpr ⟨s p.1 * e p.2, hp, e (p.2⁻¹), ⟨p.2⁻¹, rfl⟩, by simp [mul_assoc]⟩`. Combine the equalities or inequalities in the displayed calculation.

Establish `hνeq` using `Measure.isMulLeftInvariant_eq_smul ν μ`. Use `set c := ν.haarScalarFactor μ with hc_def`. Establish `hc0 : c ≠ 0`. Introduce `h0`. Establish `h : ν Set.univ = 0` using `by rw [hνeq, h0, zero_smul]; rfl`.

Rewrite `h` using `[hνapp _ MeasurableSet.univ]`. Simplify using `only [Set.preimage_univ, hm1, lintegral_const, one_mul] at h`. Conclude with `hρ (Measure.measure_univ_eq_zero.mp h)`. Establish `hcR : (c : ℝ) ≠ 0` using `NNReal.coe_ne_zero.mpr hc0`. Use `⟨(c : ℝ)⁻¹, inv_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc0)), ?_⟩` and prove the remaining obligations.

Introduce `F hF _ hFK`. Establish `h1 : ∫ y, F y ∂ν = ∫ x, F (s x) ∂ρ`. Rewrite using `[hν_def, integral_map hφ.aemeasurable hF.aestronglyMeasurable]`. Establish `h : (fun p : X × K => F (φ p)) = fun p => F (s p.1)`. Use function extensionality and compare the values at `p`.

Conclude with `hFK (s p.1) p.2`. Establish `hf` using `integral_fun_fst (μ := ρ) (ν := m) (fun x => F (s x))`. Rewrite using `[h, hf, measureReal_def, hm1]`. Simplify using the standard rewrite rules. Establish `h2 : ∫ y, F y ∂ν = ((c : ℝ) : ℂ) * ∫ y, F y ∂μ` using `by conv_lhs => rw [hνeq]`.

Rewrite using `[integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]`. Rewrite using `[← h1, h2, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hcR, Complex.ofReal_one, one_mul]`.
-/
theorem leftInvariant_of_section : ∀ {Γ K X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ] [LocallyCompactSpace Γ] [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K] [CompactSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] (e : K →* Γ) (_ : Continuous e) [MeasurableSpace X] (ρ : Measure X) [SFinite ρ] (s : X → Γ) (_ : Measurable s) (_ : ρ ≠ 0) (_ : ∀ g : Γ, ∃ a : X → X, Measurable a ∧ Measure.map a ρ = ρ ∧ ∀ᵐ x ∂ρ, ∃ k, g * s x = s (a x) * e k) (_ : ∀ A : Set Γ, IsCompact A → ρ (s ⁻¹' (A * Set.range e)) < ⊤) (μ : Measure Γ) [μ.IsHaarMeasure], ∃ c : ℝ, 0 < c ∧ ∀ F : Γ → ℂ, Continuous F → HasCompactSupport F → (∀ y k, F (y * e k) = F y) → ∫ y, F y ∂μ = c * ∫ x, F (s x) ∂ρ := by
  intro Γ K X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he _ ρ _ s hs hρ hinv hfin μ _
  obtain ⟨m, hmH, hm1⟩ : ∃ m : Measure K, m.IsHaarMeasure ∧ m Set.univ = 1 := by
    refine ⟨Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K), inferInstance, ?_⟩
    have h := Measure.haarMeasure_self (G := K) (K₀ := ⊤)
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at h
  haveI := hmH
  haveI : IsFiniteMeasure m := ⟨by rw [hm1]; exact ENNReal.one_lt_top⟩
  set φ : X × K → Γ := fun p => s p.1 * e p.2 with hφ_def
  have hφ : Measurable φ := (hs.comp measurable_fst).mul (he.measurable.comp measurable_snd)
  set ν : Measure Γ := Measure.map φ (ρ.prod m) with hν_def
  have key : ∀ (B : Set Γ) (y : Γ) (k : K),
      m ((fun k' => y * e k * e k') ⁻¹' B) = m ((fun k' => y * e k') ⁻¹' B) := by
    intro B y k
    have h : (fun k' => y * e k * e k') ⁻¹' B = (fun k' => k * k') ⁻¹' ((fun k' => y * e k') ⁻¹' B) := by
      ext k'; simp [map_mul, mul_assoc]
    rw [h, measure_preimage_mul]
  have hνapp : ∀ B : Set Γ, MeasurableSet B →
      ν B = ∫⁻ x, m ((fun k => s x * e k) ⁻¹' B) ∂ρ := by
    intro B hB
    rw [hν_def, Measure.map_apply hφ hB, Measure.prod_apply (hφ hB)]
    rfl
  have hmeasψ : ∀ B : Set Γ, MeasurableSet B →
      Measurable (fun x => m ((fun k => s x * e k) ⁻¹' B)) := by
    intro B hB
    exact measurable_measure_prodMk_left (hφ hB)
  haveI : ν.IsMulLeftInvariant := by
    constructor
    intro g
    ext B hB
    rw [Measure.map_apply (measurable_const_mul g) hB, hνapp _ (measurable_const_mul g hB), hνapp B hB]
    obtain ⟨a, ha, hamap, hae⟩ := hinv g
    calc ∫⁻ x, m ((fun k => s x * e k) ⁻¹' ((fun h => g * h) ⁻¹' B)) ∂ρ
        = ∫⁻ x, m ((fun k => s (a x) * e k) ⁻¹' B) ∂ρ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with x hx
          obtain ⟨k, hk⟩ := hx
          have h1 : (fun k' => s x * e k') ⁻¹' ((fun h => g * h) ⁻¹' B)
              = (fun k' => s (a x) * e k * e k') ⁻¹' B := by
            ext k'
            simp only [Set.mem_preimage]
            rw [← mul_assoc, hk]
          rw [h1, key]
      _ = ∫⁻ y, m ((fun k => s y * e k) ⁻¹' B) ∂(Measure.map a ρ) := by
          rw [lintegral_map (hmeasψ B hB) ha]
      _ = ∫⁻ y, m ((fun k => s y * e k) ⁻¹' B) ∂ρ := by rw [hamap]
  haveI : IsFiniteMeasureOnCompacts ν := by
    constructor
    intro A hA
    have hsub : φ ⁻¹' A ⊆ (s ⁻¹' (A * Set.range e)) ×ˢ Set.univ := by
      intro p hp
      refine ⟨?_, Set.mem_univ _⟩
      simp only [Set.mem_preimage] at hp ⊢
      exact Set.mem_mul.mpr ⟨s p.1 * e p.2, hp, e (p.2⁻¹), ⟨p.2⁻¹, rfl⟩, by simp [mul_assoc]⟩
    calc ν A = (ρ.prod m) (φ ⁻¹' A) := Measure.map_apply hφ hA.isClosed.measurableSet
      _ ≤ (ρ.prod m) ((s ⁻¹' (A * Set.range e)) ×ˢ Set.univ) := measure_mono hsub
      _ = ρ (s ⁻¹' (A * Set.range e)) * m Set.univ := Measure.prod_prod _ _
      _ < ⊤ := by rw [hm1, mul_one]; exact hfin A hA
  have hνeq := Measure.isMulLeftInvariant_eq_smul ν μ
  set c := ν.haarScalarFactor μ with hc_def
  have hc0 : c ≠ 0 := by
    intro h0
    have h : ν Set.univ = 0 := by rw [hνeq, h0, zero_smul]; rfl
    rw [hνapp _ MeasurableSet.univ] at h
    simp only [Set.preimage_univ, hm1, lintegral_const, one_mul] at h
    exact hρ (Measure.measure_univ_eq_zero.mp h)
  have hcR : (c : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hc0
  refine ⟨(c : ℝ)⁻¹, inv_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc0)), ?_⟩
  intro F hF _ hFK
  have h1 : ∫ y, F y ∂ν = ∫ x, F (s x) ∂ρ := by
    rw [hν_def, integral_map hφ.aemeasurable hF.aestronglyMeasurable]
    have h : (fun p : X × K => F (φ p)) = fun p => F (s p.1) := by
      funext p; exact hFK (s p.1) p.2
    have hf := integral_fun_fst (μ := ρ) (ν := m) (fun x => F (s x))
    rw [h, hf, measureReal_def, hm1]
    simp
  have h2 : ∫ y, F y ∂ν = ((c : ℝ) : ℂ) * ∫ y, F y ∂μ := by
    conv_lhs => rw [hνeq]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  rw [← h1, h2, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hcR, Complex.ofReal_one, one_mul]

end GlobalTheory.CompanionTheory.ConeHaar
