import Mathlib

open MeasureTheory

namespace GlobalTheory

open MeasureTheory in

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ Γ _ K hK hcov μ μ' 𝓕 𝓕' hμ h𝓕 h𝓕1 hμ' h𝓕' h𝓕'1 Φ hΦ hper`. Use `haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance`. Choose the witnesses or unpack the hypotheses as in `⟨M, hM⟩ : ∃ M, ∀ x, ‖Φ x‖ ≤ M := by`. Take `⟨M, hM⟩` from `(hK.image hΦ.norm).bddAbove`. Use `⟨M, fun x => ?_⟩` and prove the remaining obligations.

Take `⟨γ, hγ, hx⟩` from `hcov x`. Rewrite using `[← hper γ hγ x]`. Conclude with `hM ⟨_, hx, rfl⟩`. Establish `hint : IntegrableOn Φ 𝓕 μ` using `Measure.integrableOn_of_bounded (by rw [h𝓕1]; exact ENNReal.one_ne_top) hΦ.aestronglyMeasurable (M := M) (Filter.Eventually.of_forall hM)`. Use `⟨hint, ?_⟩` and prove the remaining obligations.

Establish `hsm` using `Measure.isAddLeftInvariant_eq_smul μ' μ`. Establish `hc0 : μ'.addHaarScalarFactor μ ≠ 0`. Introduce `h0`. Rewrite `hsm` using `[h0, zero_smul]`. Rewrite `h𝓕'1` using `[hsm]`.

Simplify using `at h𝓕'1`. Establish `hac : μ ≪ μ'`. Introduce `s hs`. Rewrite `hs` using `[hsm, Measure.smul_apply]`. Simplify `hs` using `[hc0]`.

Establish `h𝓕'μ : IsAddFundamentalDomain Γ 𝓕' μ` using `h𝓕'.mono hac`. Establish `hc1 : μ'.addHaarScalarFactor μ = 1`. Establish `e` using `h𝓕'1`. Rewrite `e` using `[hsm, Measure.smul_apply, h𝓕'μ.measure_eq h𝓕, h𝓕1]`. Simplify using `using e`.

Establish `hμμ' : μ' = μ` using `by rw [hsm, hc1, one_smul]`. Rewrite using `[hμμ']`. Conclude with `h𝓕.setIntegral_eq h𝓕'μ (fun g x => hper g g.2 x)`.
-/
theorem _root_.GlobalTheory.mean_periodic_indep_of_covolume_one :
    ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (μ μ' : Measure G) (𝓕 𝓕' : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → μ'.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕' μ' → μ' 𝓕' = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ∫ x in 𝓕', Φ x ∂μ' := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov μ μ' 𝓕 𝓕' hμ h𝓕 h𝓕1 hμ' h𝓕' h𝓕'1 Φ hΦ hper
  haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, ‖Φ x‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hK.image hΦ.norm).bddAbove
    refine ⟨M, fun x => ?_⟩
    obtain ⟨γ, hγ, hx⟩ := hcov x
    rw [← hper γ hγ x]
    exact hM ⟨_, hx, rfl⟩
  have hint : IntegrableOn Φ 𝓕 μ :=
    Measure.integrableOn_of_bounded (by rw [h𝓕1]; exact ENNReal.one_ne_top)
      hΦ.aestronglyMeasurable (M := M) (Filter.Eventually.of_forall hM)
  refine ⟨hint, ?_⟩
  have hsm := Measure.isAddLeftInvariant_eq_smul μ' μ
  have hc0 : μ'.addHaarScalarFactor μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hsm
    rw [hsm] at h𝓕'1
    simp at h𝓕'1
  have hac : μ ≪ μ' := by
    intro s hs
    rw [hsm, Measure.smul_apply] at hs
    simpa [hc0] using hs
  have h𝓕'μ : IsAddFundamentalDomain Γ 𝓕' μ := h𝓕'.mono hac
  have hc1 : μ'.addHaarScalarFactor μ = 1 := by
    have e := h𝓕'1
    rw [hsm, Measure.smul_apply, h𝓕'μ.measure_eq h𝓕, h𝓕1] at e
    simpa using e
  have hμμ' : μ' = μ := by rw [hsm, hc1, one_smul]
  rw [hμμ']
  exact h𝓕.setIntegral_eq h𝓕'μ (fun g x => hper g g.2 x)

end GlobalTheory
