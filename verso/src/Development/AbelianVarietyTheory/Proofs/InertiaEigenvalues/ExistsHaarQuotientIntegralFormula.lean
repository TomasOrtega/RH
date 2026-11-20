import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR MeasureTheory Filter Topology

namespace GlobalTheory.JR

open TopologicalGroup in

/- English proof (translation)
Establish `key : ∀ L : ℂ →L[ℝ] ℝ, L (∫ b, F b ∂(H.inducedMeasure ν μC)) = L (∫ c, H.pushforward ν F c ∂μC)`. Introduce `L`. Set `G : CompactlySupportedContinuousMap B ℝ` to `⟨⟨fun b => L (F b), L.continuous.comp F.continuous⟩, F.hasCompactSupport.comp_left (g := L) (map_zero L)⟩`. Rewrite using `[← L.integral_comp_comm F.integrable, ← L.integral_comp_comm (H.pushforward ν F).integrable]`. Establish `h1` using `H.integral_inducedMeasure ν μC G`.

Rewrite `h1` using `[IsSES.integrate_apply]`. Use `h1.trans ?_` and prove the remaining obligations. Use `congr with c`. Rewrite using `[IsSES.pushforward_def, IsSES.pushforward_def, ← L.integral_comp_comm (H.pullback F _).integrable]`. Simplify using `only [IsSES.pullback_def]`.

Both sides reduce to the same expression. Conclude with `Complex.ext (key Complex.reCLM) (key Complex.imCLM)`.
-/
theorem integral_inducedMeasure_complex {A B C : Type} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [IsTopologicalGroup A]
    [IsTopologicalGroup B] [IsTopologicalGroup C] [T2Space B] [LocallyCompactSpace B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B] [MeasurableSpace C]
    [BorelSpace C] {φ : A →* B} {ψ : B →* C} (H : IsSES φ ψ) (ν : Measure A) [ν.IsHaarMeasure]
    (μC : Measure C) [μC.IsHaarMeasure] (F : CompactlySupportedContinuousMap B ℂ) :
    ∫ b, F b ∂(H.inducedMeasure ν μC) = ∫ c, H.pushforward ν F c ∂μC := by
  have key : ∀ L : ℂ →L[ℝ] ℝ, L (∫ b, F b ∂(H.inducedMeasure ν μC))
      = L (∫ c, H.pushforward ν F c ∂μC) := by
    intro L
    let G : CompactlySupportedContinuousMap B ℝ :=
      ⟨⟨fun b => L (F b), L.continuous.comp F.continuous⟩,
        F.hasCompactSupport.comp_left (g := L) (map_zero L)⟩
    rw [← L.integral_comp_comm F.integrable,
      ← L.integral_comp_comm (H.pushforward ν F).integrable]
    have h1 := H.integral_inducedMeasure ν μC G
    rw [IsSES.integrate_apply] at h1
    refine h1.trans ?_
    congr with c
    rw [IsSES.pushforward_def, IsSES.pushforward_def,
      ← L.integral_comp_comm (H.pullback F _).integrable]
    simp only [IsSES.pullback_def]
    rfl
  exact Complex.ext (key Complex.reCLM) (key Complex.imCLM)

/- English proof (translation)
Introduce `A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ ψ H μB μC hB hC`. Establish `: LocallyCompactSpace A` using `H.isClosedEmbedding.locallyCompactSpace`. Set `ν0 : Measure A` to `Measure.haar`. Use `set μ := H.inducedMeasure ν0 μC with hμ`. Establish `hsm` using `Measure.isMulLeftInvariant_eq_smul μB μ`.

Establish `hpos` using `Measure.haarScalarFactor_pos_of_isHaarMeasure μB μ`. Use `set k := Measure.haarScalarFactor μB μ with hk`. Use `⟨k • ν0, Measure.IsHaarMeasure.nnreal_smul ν0 hpos.ne', ?_⟩` and prove the remaining obligations. Introduce `f hf hfc s hs`. Set `F : CompactlySupportedContinuousMap B ℂ` to `⟨⟨f, hf⟩, hfc⟩`.

Establish `h` using `integral_inducedMeasure_complex H ν0 μC F`. Rewrite using `[hsm, integral_smul_nnreal_measure]`. Repeatedly rewrite using `[integral_smul_nnreal_measure, NNReal.smul_def]`. Rewrite using `[integral_smul]`. Use `congr 1`.

Use `h.trans ?_` and prove the remaining obligations. Use `congr with c`. Use `conv_lhs => rw [← hs c]`. Rewrite using `[H.pushforward_apply_apply]`. Simplify using `only [TopologicalGroup.IsSES.pullback_def]`.

Both sides reduce to the same expression.
-/
theorem exists_haar_quotient_integral_formula : ∀ (A B C : Type) [Group A] [Group B] [Group C] [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C] [T2Space B] [LocallyCompactSpace B] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B] [MeasurableSpace C] [BorelSpace C] (φ : A →* B) (ψ : B →* C), TopologicalGroup.IsSES φ ψ → ∀ (μB : Measure B) (μC : Measure C), μB.IsHaarMeasure → μC.IsHaarMeasure → ∃ ν : Measure A, ν.IsHaarMeasure ∧ ∀ f : B → ℂ, Continuous f → HasCompactSupport f → ∀ s : C → B, (∀ c, ψ (s c) = c) → ∫ b, f b ∂μB = ∫ c, ∫ a, f (s c * φ a) ∂ν ∂μC := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ ψ H μB μC hB hC
  have : LocallyCompactSpace A := H.isClosedEmbedding.locallyCompactSpace
  let ν0 : Measure A := Measure.haar
  set μ := H.inducedMeasure ν0 μC with hμ
  have hsm := Measure.isMulLeftInvariant_eq_smul μB μ
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure μB μ
  set k := Measure.haarScalarFactor μB μ with hk
  refine ⟨k • ν0, Measure.IsHaarMeasure.nnreal_smul ν0 hpos.ne', ?_⟩
  intro f hf hfc s hs
  let F : CompactlySupportedContinuousMap B ℂ := ⟨⟨f, hf⟩, hfc⟩
  have h := integral_inducedMeasure_complex H ν0 μC F
  rw [hsm, integral_smul_nnreal_measure]
  simp_rw [integral_smul_nnreal_measure, NNReal.smul_def]
  rw [integral_smul]
  congr 1
  refine h.trans ?_
  congr with c
  conv_lhs => rw [← hs c]
  rw [H.pushforward_apply_apply]
  simp only [TopologicalGroup.IsSES.pullback_def]
  rfl

end GlobalTheory.JR
