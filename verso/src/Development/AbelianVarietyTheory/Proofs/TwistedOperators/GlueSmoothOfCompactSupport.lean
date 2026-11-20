import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DixmierMalliavinLie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransChartSymmApply
open GlobalTheory.Orb
open scoped Topology ContDiff Manifold

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Introduce `H _ X _ _ _ c f hc hf hloc`. Use `choose V hVo hcV Φ hΦ hfΦ using hloc`. Establish `hs : IsClosed (c '' tsupport f)` using `(hf.isCompact.image hc).isClosed`. Establish `hcov : c '' tsupport f ⊆ ⋃ a, V a`. Introduce and unpack `_ ⟨a, -, rfl⟩`.

Conclude with `Set.mem_iUnion.2 ⟨a, hcV a⟩`. Take `⟨χ, hχ⟩` from `SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, X) hs V hVo hcov`. Use `⟨fun y => ∑ᶠ a, χ a y • Φ a y, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `y`.

Use `χ.contDiffAt_finsum fun a hy => ?_` and prove the remaining obligations. Conclude with `(hΦ a).contDiffAt ((hVo a).mem_nhds (hχ a hy))`. Introduce `g`. Establish `hterm : ∀ a, χ a (c g) • Φ a (c g) = χ a (c g) • f g`. Introduce `a`.

Distinguish the cases in `h0 : χ a (c g) = 0`. Simplify using `[h0]`. Establish `hmem : c g ∈ V a` using `hχ a (subset_tsupport _ h0)`. Rewrite using `[hfΦ a g hmem]`. Simplify using `only [hterm]`.

Distinguish the cases in `hg : g ∈ tsupport f`. Rewrite using `[← finsum_smul, χ.sum_eq_one ⟨g, hg, rfl⟩, one_smul]`. Establish `: f g = 0` using `image_eq_zero_of_notMem_tsupport hg`. Simplify using `[this]`.
-/
theorem glue_smooth_of_compactSupport : ∀ (H : Type) [TopologicalSpace H] (X : Type) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] (c : H → X) (f : H → ℂ), Continuous c →
    HasCompactSupport f →
    (∀ a, ∃ V : Set X, IsOpen V ∧ c a ∈ V ∧ ∃ Φ : X → ℂ, ContDiffOn ℝ ∞ Φ V ∧
      ∀ g, c g ∈ V → f g = Φ (c g)) →
    ∃ Φ : X → ℂ, ContDiff ℝ ∞ Φ ∧ ∀ g, f g = Φ (c g) := by
  intro H _ X _ _ _ c f hc hf hloc
  choose V hVo hcV Φ hΦ hfΦ using hloc
  have hs : IsClosed (c '' tsupport f) := (hf.isCompact.image hc).isClosed
  have hcov : c '' tsupport f ⊆ ⋃ a, V a := by
    rintro _ ⟨a, -, rfl⟩
    exact Set.mem_iUnion.2 ⟨a, hcV a⟩
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, X) hs V hVo hcov
  refine ⟨fun y => ∑ᶠ a, χ a y • Φ a y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    refine χ.contDiffAt_finsum fun a hy => ?_
    exact (hΦ a).contDiffAt ((hVo a).mem_nhds (hχ a hy))
  · intro g
    have hterm : ∀ a, χ a (c g) • Φ a (c g) = χ a (c g) • f g := by
      intro a
      by_cases h0 : χ a (c g) = 0
      · simp [h0]
      · have hmem : c g ∈ V a := hχ a (subset_tsupport _ h0)
        rw [hfΦ a g hmem]
    simp only [hterm]
    by_cases hg : g ∈ tsupport f
    · rw [← finsum_smul, χ.sum_eq_one ⟨g, hg, rfl⟩, one_smul]
    · have : f g = 0 := image_eq_zero_of_notMem_tsupport hg
      simp [this]

end GlobalTheory
