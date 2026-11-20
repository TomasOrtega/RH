import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology Pointwise

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ N a H ν _ hN hinv hray ψ hψ hc`. Establish `hint : ∀ g, Integrable (fun m => ψ (g * m)) ν` using `fun g => (hψ.comp (continuous_const.mul continuous_id)).integrable_of_hasCompactSupport (hc.comp_homeomorph (Homeomorph.mulLeft g))`. Establish `hcont : Continuous (fun g => ∫ m, ψ (g * m) ∂ν)`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `g₀`.

Take `⟨U, hU, hUn⟩` from `exists_compact_mem_nhds g₀`. Establish `hk : IsCompact (U⁻¹ * tsupport ψ)` using `hU.inv.mul hc`. Establish `h` using `continuousOn_integral_of_compact_support (μ := ν) (f := fun g m => ψ (g * m)) (s := U) hk (hψ.comp (continuous_fst.mul continuous_snd)).continuousOn (fun p x hp hx => by`. Assume the negation of the conclusion as `hne`. Conclude with `hx ⟨p⁻¹, Set.inv_mem_inv.2 hp, p * x, subset_tsupport ψ hne, by simp⟩)`.

Conclude with `h.continuousAt hUn`. Establish `hI : ∀ g, ∀ m ∈ N, (∫ x, ψ (g * m * x) ∂ν) = ∫ x, ψ (g * x) ∂ν`. Introduce `g m hm`. Establish `h` using `integral_map_equiv (μ := ν) (MeasurableEquiv.mulLeft m) (fun x => ψ (g * x))`. Establish `h2 : ν.map (MeasurableEquiv.mulLeft m) = ν` using `hinv m hm`.

Rewrite `h` using `[h2]`. Rewrite using `[h]`. Simplify using `[mul_assoc]`. Establish `hex : ∀ g, (∫ m, ψ (g * m) ∂ν) ≠ 0 → ∃ m ∈ N, g * m ∈ tsupport ψ`. Introduce `g hg`.

Assume the negation of the conclusion as `hne`. Apply `hg` to reduce the goal to its premises. Apply `integral_eq_zero_of_ae` to reduce the goal to its premises. Establish `hae : ∀ᵐ m ∂ν, m ∈ N` using `hN`. Use `filter_upwards [hae] with m hm`.

Assume the negation of the conclusion as `h0`. Conclude with `hne ⟨m, hm, subset_tsupport ψ h0⟩`. Use `⟨⟨hcont, ?_, hI, ?_⟩, hint⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `(IsCompact.image hc hcont.norm).bddAbove`. Use `⟨max C 0, fun g => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hg : (∫ m, ψ (g * m) ∂ν) = 0`. Simplify using `[hg]`. Take `⟨m, hm, hs⟩` from `hex g hg`. Use `hC ⟨g * m, hs, rfl⟩` as an intermediate fact. Simplify using `only [hI g m hm] at this`.

Conclude with `this.trans (le_max_left _ _)`. Take `⟨R, hR⟩` from `(IsCompact.image hc hray.contH.abs).bddAbove`. Use `⟨R, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨m, hm, hs⟩` from `hex g hg`. Use `hR ⟨g * m, hs, rfl⟩` as an intermediate fact.

Simplify `this` using `only [hray.inv g m hm]`.
-/
theorem UpperTheory.Lit.Cusp.isBand_of_compact :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (N : Set G) (a : ℝ → G) (H : G → ℝ)
      (ν : Measure G) [IsFiniteMeasureOnCompacts ν], ν Nᶜ = 0 → (∀ m ∈ N, ν.map (fun x => m * x) = ν) →
      IsRay N a H → ∀ ψ : G → ℂ, Continuous ψ → HasCompactSupport ψ →
        IsBand N H (fun g => ∫ m, ψ (g * m) ∂ν) ∧ ∀ g, Integrable (fun m => ψ (g * m)) ν := by
  intro G _ _ _ _ _ _ _ _ N a H ν _ hN hinv hray ψ hψ hc
  have hint : ∀ g, Integrable (fun m => ψ (g * m)) ν := fun g =>
    (hψ.comp (continuous_const.mul continuous_id)).integrable_of_hasCompactSupport
      (hc.comp_homeomorph (Homeomorph.mulLeft g))
  have hcont : Continuous (fun g => ∫ m, ψ (g * m) ∂ν) := by
    rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨U, hU, hUn⟩ := exists_compact_mem_nhds g₀
    have hk : IsCompact (U⁻¹ * tsupport ψ) := hU.inv.mul hc
    have h := continuousOn_integral_of_compact_support (μ := ν) (f := fun g m => ψ (g * m)) (s := U) hk
      (hψ.comp (continuous_fst.mul continuous_snd)).continuousOn (fun p x hp hx => by
        by_contra hne
        exact hx ⟨p⁻¹, Set.inv_mem_inv.2 hp, p * x, subset_tsupport ψ hne, by simp⟩)
    exact h.continuousAt hUn
  have hI : ∀ g, ∀ m ∈ N, (∫ x, ψ (g * m * x) ∂ν) = ∫ x, ψ (g * x) ∂ν := by
    intro g m hm
    have h := integral_map_equiv (μ := ν) (MeasurableEquiv.mulLeft m) (fun x => ψ (g * x))
    have h2 : ν.map (MeasurableEquiv.mulLeft m) = ν := hinv m hm
    rw [h2] at h
    rw [h]
    simp [mul_assoc]
  have hex : ∀ g, (∫ m, ψ (g * m) ∂ν) ≠ 0 → ∃ m ∈ N, g * m ∈ tsupport ψ := by
    intro g hg
    by_contra hne
    apply hg
    apply integral_eq_zero_of_ae
    have hae : ∀ᵐ m ∂ν, m ∈ N := hN
    filter_upwards [hae] with m hm
    by_contra h0
    exact hne ⟨m, hm, subset_tsupport ψ h0⟩
  refine ⟨⟨hcont, ?_, hI, ?_⟩, hint⟩
  · obtain ⟨C, hC⟩ := (IsCompact.image hc hcont.norm).bddAbove
    refine ⟨max C 0, fun g => ?_⟩
    by_cases hg : (∫ m, ψ (g * m) ∂ν) = 0
    · simp [hg]
    · obtain ⟨m, hm, hs⟩ := hex g hg
      have := hC ⟨g * m, hs, rfl⟩
      simp only [hI g m hm] at this
      exact this.trans (le_max_left _ _)
  · obtain ⟨R, hR⟩ := (IsCompact.image hc hray.contH.abs).bddAbove
    refine ⟨R, fun g hg => ?_⟩
    obtain ⟨m, hm, hs⟩ := hex g hg
    have := hR ⟨g * m, hs, rfl⟩
    simpa only [hray.inv g m hm] using this
