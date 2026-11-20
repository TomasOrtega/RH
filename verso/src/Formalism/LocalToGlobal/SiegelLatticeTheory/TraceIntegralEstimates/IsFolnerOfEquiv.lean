import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.FolnerAbs

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Measure Filter Topology
open scoped ENNReal

namespace Formalism.L2.S.Pv.FolnerT

open Formalism.L2.SG.Pf.EnergyAbs

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

/- English proof (translation)
Take `⟨hC, h1, hm, hi, hσ, h0, hc, hl, hK, hr, hinv⟩` from `hμ`. Establish `hs : Measurable Φ.symm` using `hΦ'.measurable`. Set `E : G ≃ₜ H` to `{ Φ.toEquiv with continuous_toFun := hΦ, continuous_invFun := hΦ' }`. Set `M : G ≃ᵐ H` to `E.toMeasurableEquiv`. Establish `hmap : ∀ A : Set G, (μ.map Φ.symm) A = μ (Φ.symm ⁻¹' A)` using `fun A => by`.

Conclude with `MeasurableEquiv.map_apply M.symm A`. Use `⟨hC.preimage hΦ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show Φ 1 ∈ S`. Rewrite using `[map_one]`. Conclude with `h1`.

Introduce `a ha b hb show Φ (a * b) ∈ S`. Rewrite using `[map_mul]`. Conclude with `hm _ ha _ hb`. Introduce `a ha show Φ a⁻¹ ∈ S`. Rewrite using `[map_inv]`.

Conclude with `hi _ ha`. Use `haveI := hσ show SigmaFinite (μ.map M.symm) first`. Consider the case `exact M.symm.sigmaFinite_map`. Consider the case `exact MeasurableEquiv.sigmaFinite_map M.symm`. Consider the case `(refine SigmaFinite.of_map _ M.measurable.aemeasurable ?_`.

Rewrite using `[Measure.map_map M.measurable M.symm.measurable, M.self_comp_symm, Measure.map_id]`. Conclude with `hσ)`. Introduce `h`. Conclude with `h0 ((Measure.map_eq_zero_iff hs.aemeasurable).1 h)`. Rewrite using `[hmap]`.

Use `hc using 2` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using the standard rewrite rules. Introduce `s hsS`. Rewrite using `[Measure.map_map (continuous_mul_left s).measurable hs]`.

Establish `e1 : (fun x => s * x) ∘ ⇑Φ.symm = ⇑Φ.symm ∘ (fun y => Φ s * y)`. Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules. Rewrite using `[e1, ← Measure.map_map hs (continuous_mul_left (Φ s)).measurable, hl _ hsS]`. Introduce `K hKc`.

Rewrite using `[hmap]`. Conclude with `hK _ ((E.symm.isCompact_preimage).2 hKc)`. Introduce `s hsS`. Rewrite using `[Measure.map_map (continuous_mul_right s).measurable hs]`. Establish `e1 : (fun x => x * s) ∘ ⇑Φ.symm = ⇑Φ.symm ∘ (fun y => y * Φ s)`.

Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules. Rewrite using `[e1, ← Measure.map_map hs (continuous_mul_right (Φ s)).measurable, hr _ hsS]`. Rewrite using `[Measure.map_map continuous_inv.measurable hs]`. Establish `e1 : (fun x : G => x⁻¹) ∘ ⇑Φ.symm = ⇑Φ.symm ∘ (fun y => y⁻¹)`.

Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules. Rewrite using `[e1, ← Measure.map_map hs continuous_inv.measurable, hinv]`.
-/
theorem isHaarSub_comap (Φ : G ≃* H) (hΦ : Continuous Φ) (hΦ' : Continuous Φ.symm) {S : Set H} {μ : Measure H}
    (hμ : IsHaarSub S μ) : IsHaarSub (Φ ⁻¹' S) (μ.map Φ.symm) := by
  obtain ⟨hC, h1, hm, hi, hσ, h0, hc, hl, hK, hr, hinv⟩ := hμ
  have hs : Measurable Φ.symm := hΦ'.measurable
  let E : G ≃ₜ H := { Φ.toEquiv with continuous_toFun := hΦ, continuous_invFun := hΦ' }
  let M : G ≃ᵐ H := E.toMeasurableEquiv
  have hmap : ∀ A : Set G, (μ.map Φ.symm) A = μ (Φ.symm ⁻¹' A) := fun A => by
    exact MeasurableEquiv.map_apply M.symm A
  refine ⟨hC.preimage hΦ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Φ 1 ∈ S
    rw [map_one]
    exact h1
  · intro a ha b hb
    show Φ (a * b) ∈ S
    rw [map_mul]
    exact hm _ ha _ hb
  · intro a ha
    show Φ a⁻¹ ∈ S
    rw [map_inv]
    exact hi _ ha
  · haveI := hσ
    show SigmaFinite (μ.map M.symm)
    first
      | exact M.symm.sigmaFinite_map
      | exact MeasurableEquiv.sigmaFinite_map M.symm
      | (refine SigmaFinite.of_map _ M.measurable.aemeasurable ?_
         rw [Measure.map_map M.measurable M.symm.measurable, M.self_comp_symm, Measure.map_id]
         exact hσ)
  · intro h
    exact h0 ((Measure.map_eq_zero_iff hs.aemeasurable).1 h)
  · rw [hmap]
    convert hc using 2
    ext x
    simp
  · intro s hsS
    rw [Measure.map_map (continuous_mul_left s).measurable hs]
    have e1 : (fun x => s * x) ∘ ⇑Φ.symm = ⇑Φ.symm ∘ (fun y => Φ s * y) := by
      funext y
      simp
    rw [e1, ← Measure.map_map hs (continuous_mul_left (Φ s)).measurable, hl _ hsS]
  · intro K hKc
    rw [hmap]
    exact hK _ ((E.symm.isCompact_preimage).2 hKc)
  · intro s hsS
    rw [Measure.map_map (continuous_mul_right s).measurable hs]
    have e1 : (fun x => x * s) ∘ ⇑Φ.symm = ⇑Φ.symm ∘ (fun y => y * Φ s) := by
      funext y
      simp
    rw [e1, ← Measure.map_map hs (continuous_mul_right (Φ s)).measurable, hr _ hsS]
  · rw [Measure.map_map continuous_inv.measurable hs]
    have e1 : (fun x : G => x⁻¹) ∘ ⇑Φ.symm = ⇑Φ.symm ∘ (fun y => y⁻¹) := by
      funext y
      simp
    rw [e1, ← Measure.map_map hs continuous_inv.measurable, hinv]

/- English proof (translation)
Establish `hs : Measurable Φ.symm` using `hΦ'.measurable`. Set `E : G ≃ₜ H` to `{ Φ.toEquiv with continuous_toFun := hΦ, continuous_invFun := hΦ' }`. Set `M : G ≃ᵐ H` to `E.toMeasurableEquiv`. Establish `hmap : ∀ A : Set G, (μ.map Φ.symm) A = μ (Φ.symm ⁻¹' A)` using `fun A => by`. Conclude with `MeasurableEquiv.map_apply M.symm A`.

Introduce `K hK hKS ε hε`. Take `⟨Ω, hΩm, hΩS, hpos, hfin, hle⟩` from `hF (Φ ⁻¹' K) ((E.isCompact_preimage).2 hK) (Set.preimage_mono hKS) ε hε`. Use `⟨Φ.symm ⁻¹' Ω, hs hΩm, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Use `hΩS hx` as an intermediate fact.

Simplify using `using this`. Rewrite using `[← hmap]`. Conclude with `hpos`. Rewrite using `[← hmap]`. Conclude with `hfin`.

Establish `hset : {t | t ∈ ⇑Φ.symm ⁻¹' Ω ∧ ∀ k ∈ K, k * t ∈ ⇑Φ.symm ⁻¹' Ω} = ⇑Φ.symm ⁻¹' {t | t ∈ Ω ∧ ∀ k ∈ ⇑Φ ⁻¹' K, k * t ∈ Ω}`. Use extensionality with `t`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, map_mul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Use `⟨h1, fun k hk => ?_⟩` and prove the remaining obligations. Use `h2 (Φ k) hk` as an intermediate fact. Rewrite `this` using `[MulEquiv.symm_apply_apply]`. Then use the resulting hypothesis. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, fun k hk => ?_⟩` and prove the remaining obligations.

Conclude with `h2 (Φ.symm k) (by simpa using hk)`. Rewrite using `[hset, ← hmap, ← hmap]`. Conclude with `hle`.
-/
theorem isFolner_of_equiv (Φ : G ≃* H) (hΦ : Continuous Φ) (hΦ' : Continuous Φ.symm) {S : Set H} {μ : Measure H}
    (hμ : IsHaarSub S μ) (hF : IsFolner (Φ ⁻¹' S) (μ.map Φ.symm)) : IsFolner S μ := by
  have hs : Measurable Φ.symm := hΦ'.measurable
  let E : G ≃ₜ H := { Φ.toEquiv with continuous_toFun := hΦ, continuous_invFun := hΦ' }
  let M : G ≃ᵐ H := E.toMeasurableEquiv
  have hmap : ∀ A : Set G, (μ.map Φ.symm) A = μ (Φ.symm ⁻¹' A) := fun A => by
    exact MeasurableEquiv.map_apply M.symm A
  intro K hK hKS ε hε
  obtain ⟨Ω, hΩm, hΩS, hpos, hfin, hle⟩ :=
    hF (Φ ⁻¹' K) ((E.isCompact_preimage).2 hK) (Set.preimage_mono hKS) ε hε
  refine ⟨Φ.symm ⁻¹' Ω, hs hΩm, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have := hΩS hx
    simpa using this
  · rw [← hmap]
    exact hpos
  · rw [← hmap]
    exact hfin
  · have hset : {t | t ∈ ⇑Φ.symm ⁻¹' Ω ∧ ∀ k ∈ K, k * t ∈ ⇑Φ.symm ⁻¹' Ω} =
        ⇑Φ.symm ⁻¹' {t | t ∈ Ω ∧ ∀ k ∈ ⇑Φ ⁻¹' K, k * t ∈ Ω} := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun k hk => ?_⟩
        have := h2 (Φ k) hk
        rwa [MulEquiv.symm_apply_apply] at this
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun k hk => ?_⟩
        exact h2 (Φ.symm k) (by simpa using hk)
    rw [hset, ← hmap, ← hmap]
    exact hle

end Formalism.L2.S.Pv.FolnerT
