import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Establish `hfib : ∀ g, π ⁻¹' {π g} = (fun x => x * g⁻¹) ⁻¹' H`. Introduce `g`. Use extensionality with `x`. Simplify using `[hπ g x]`. Establish `hfibO : ∀ g, IsOpen (π ⁻¹' {π g})`.

Introduce `g`. Rewrite using `[hfib g]`. Conclude with `hH.preimage (continuous_mul_right _)`. Establish `hfibM : ∀ l, MeasurableSet (π ⁻¹' {l})`. Introduce `l`.

Distinguish the cases in `hl : l ∈ Set.range π`. Take `⟨g, rfl⟩` from `hl`. Conclude with `(hfibO g).measurableSet`. Establish `: π ⁻¹' {l} = ∅`. Use extensionality with `x`.

Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]`. Conclude with `fun h => hl ⟨x, h⟩`. Rewrite using `[this]`. Conclude with `MeasurableSet.empty`. Establish `hfib1 : ∀ g, μ (π ⁻¹' {π g}) = 1`.

Introduce `g`. Rewrite using `[hfib g, measure_preimage_mul_right, hμ]`. Use `set S := Set.range π ∩ Function.support s with hSdef`. Distinguish the cases in `hS : S.Finite`. Use `set T := hS.toFinset with hT`.

Establish `hfun : (fun g => s (π g)) = fun g => ∑ l ∈ T, (π ⁻¹' {l}).indicator (fun _ => s l) g`. Use function extensionality and compare the values at `g`. Establish `: ∀ l, (π ⁻¹' {l}).indicator (fun _ => s l) g = if π g = l then s (π g) else 0`. Introduce `l`. Distinguish the cases in `h : π g = l`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Set.indicator_apply, h]`. Simplify using `only [this, Finset.sum_ite_eq]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Establish `: π g ∉ S` using `by rw [hT, Set.Finite.mem_toFinset] at *; exact h`. Assume the negation of the conclusion as `hne`. Conclude with `this ⟨⟨g, rfl⟩, Ne.symm hne |>.symm⟩`. Rewrite using `[hfun, integral_finset_sum]`.

Rewrite using `[← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hS]`. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Introduce `l hl`. Rewrite using `[integral_indicator_const _ (hfibM l)]`. Establish `hl' : l ∈ Set.range π` using `((Set.Finite.mem_toFinset hS).1 hl).1`.

Take `⟨g, rfl⟩` from `hl'`. Simplify using `[Measure.real, hfib1 g]`. Introduce `l _`. Conclude with `(integrable_indicator_iff (hfibM l)).2 (by`. Distinguish the cases in `hl : l ∈ Set.range π`.

Take `⟨g, rfl⟩` from `hl haveI : IsFiniteMeasure (μ.restrict (π ⁻¹' {π g})) := ⟨by simp [hfib1 g]⟩`. Conclude with `integrable_const _`. Establish `: π ⁻¹' {l} = ∅`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]`.

Conclude with `fun h => hl ⟨x, h⟩`. Rewrite using `[this]`. Conclude with `integrableOn_empty)`. Rewrite using `[finsum_mem_eq_zero_of_infinite hS]`. Apply `integral_undef` to reduce the goal to its premises.

Introduce `hint`. Establish `hfin` using `hint.2`. Establish `hbound : ∀ F : Finset Λ, (↑F : Set Λ) ⊆ S → (F.card : ENNReal) ≤ ∫⁻ g, ‖s (π g)‖ₑ ∂μ`. Introduce `F hF`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.card_eq_sum_ones, Nat.cast_sum]`. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Introduce `l hl`. Take `⟨⟨g, rfl⟩, _⟩` from `hF hl`. Simplify using `[hfib1 g]`.

Use `_ = ∫⁻ g, ∑ l ∈ F, (π ⁻¹' {l}).indicator 1 g ∂μ := by`. Rewrite using `[lintegral_finset_sum]`. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Introduce `l _`. Rewrite using `[lintegral_indicator_one (hfibM l)]`.

Introduce `l _`. Conclude with `(measurable_one.indicator (hfibM l))`. Use `_ ≤ ∫⁻ g, ‖s (π g)‖ₑ ∂μ := by`. Apply `lintegral_mono` to reduce the goal to its premises. Introduce `g`.

Establish `: ∀ l, (π ⁻¹' {l}).indicator (1 : G → ENNReal) g = if π g = l then 1 else 0`. Introduce `l`. Simplify using `[Set.indicator_apply]`. Simplify using `only [this, Finset.sum_ite_eq]`. Use `split_ifs with h`.

Take `⟨_, hsupp⟩` from `hF h`. Break down `hs (π g) with h0 | h1` into its components or cases. Conclude with `absurd h0 hsupp`. Rewrite using `[← ofReal_norm_eq_enorm, h1]`. Simplify using the standard rewrite rules.

Conclude with `bot_le`. Take `⟨n, hn⟩` from `ENNReal.exists_nat_gt hfin.ne`. Take `⟨F, hFS, hFc⟩` from `Set.Infinite.exists_subset_card_eq (hS : S.Infinite) n`. Use `hbound F hFS` as an intermediate fact. Rewrite `this` using `[hFc]`.

Conclude with `absurd (lt_of_le_of_lt this hn) (lt_irrefl _)`.
-/
theorem integral_rightCoset_fun_eq_finsum (G Λ : Type) [Group G] [TopologicalSpace G] [ContinuousMul G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulRightInvariant] (H : Set G)
    (hH : IsOpen H) (hμ : μ H = 1) (π : G → Λ) (hπ : ∀ g g', π g' = π g ↔ g' * g⁻¹ ∈ H)
    (s : Λ → ℂ) (hs : ∀ l, s l = 0 ∨ ‖s l‖ = 1) :
    ∫ g, s (π g) ∂μ = ∑ᶠ l ∈ Set.range π, s l := by
  classical

  have hfib : ∀ g, π ⁻¹' {π g} = (fun x => x * g⁻¹) ⁻¹' H := by
    intro g; ext x; simp [hπ g x]
  have hfibO : ∀ g, IsOpen (π ⁻¹' {π g}) := by
    intro g; rw [hfib g]; exact hH.preimage (continuous_mul_right _)
  have hfibM : ∀ l, MeasurableSet (π ⁻¹' {l}) := by
    intro l
    by_cases hl : l ∈ Set.range π
    · obtain ⟨g, rfl⟩ := hl; exact (hfibO g).measurableSet
    · have : π ⁻¹' {l} = ∅ := by
        ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun h => hl ⟨x, h⟩
      rw [this]; exact MeasurableSet.empty
  have hfib1 : ∀ g, μ (π ⁻¹' {π g}) = 1 := by
    intro g; rw [hfib g, measure_preimage_mul_right, hμ]
  set S := Set.range π ∩ Function.support s with hSdef
  by_cases hS : S.Finite
  · set T := hS.toFinset with hT
    have hfun : (fun g => s (π g)) = fun g => ∑ l ∈ T, (π ⁻¹' {l}).indicator (fun _ => s l) g := by
      funext g
      have : ∀ l, (π ⁻¹' {l}).indicator (fun _ => s l) g = if π g = l then s (π g) else 0 := by
        intro l
        by_cases h : π g = l
        · subst h; simp
        · simp [Set.indicator_apply, h]
      simp only [this, Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · have : π g ∉ S := by rw [hT, Set.Finite.mem_toFinset] at *; exact h
        by_contra hne
        exact this ⟨⟨g, rfl⟩, Ne.symm hne |>.symm⟩
    rw [hfun, integral_finset_sum]
    · rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hS]
      refine Finset.sum_congr rfl ?_
      intro l hl
      rw [integral_indicator_const _ (hfibM l)]
      have hl' : l ∈ Set.range π := ((Set.Finite.mem_toFinset hS).1 hl).1
      obtain ⟨g, rfl⟩ := hl'
      simp [Measure.real, hfib1 g]
    · intro l _
      exact (integrable_indicator_iff (hfibM l)).2 (by
        by_cases hl : l ∈ Set.range π
        · obtain ⟨g, rfl⟩ := hl
          haveI : IsFiniteMeasure (μ.restrict (π ⁻¹' {π g})) := ⟨by simp [hfib1 g]⟩
          exact integrable_const _
        · have : π ⁻¹' {l} = ∅ := by
            ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
            exact fun h => hl ⟨x, h⟩
          rw [this]; exact integrableOn_empty)
  · rw [finsum_mem_eq_zero_of_infinite hS]
    apply integral_undef
    intro hint
    have hfin := hint.2

    have hbound : ∀ F : Finset Λ, (↑F : Set Λ) ⊆ S → (F.card : ENNReal) ≤ ∫⁻ g, ‖s (π g)‖ₑ ∂μ := by
      intro F hF
      calc (F.card : ENNReal) = ∑ l ∈ F, μ (π ⁻¹' {l}) := by
            rw [Finset.card_eq_sum_ones, Nat.cast_sum]
            refine Finset.sum_congr rfl ?_
            intro l hl
            obtain ⟨⟨g, rfl⟩, _⟩ := hF hl
            simp [hfib1 g]
        _ = ∫⁻ g, ∑ l ∈ F, (π ⁻¹' {l}).indicator 1 g ∂μ := by
            rw [lintegral_finset_sum]
            · refine Finset.sum_congr rfl ?_
              intro l _
              rw [lintegral_indicator_one (hfibM l)]
            · intro l _
              exact (measurable_one.indicator (hfibM l))
        _ ≤ ∫⁻ g, ‖s (π g)‖ₑ ∂μ := by
            apply lintegral_mono
            intro g
            have : ∀ l, (π ⁻¹' {l}).indicator (1 : G → ENNReal) g = if π g = l then 1 else 0 := by
              intro l; simp [Set.indicator_apply]
            simp only [this, Finset.sum_ite_eq]
            split_ifs with h
            · obtain ⟨_, hsupp⟩ := hF h
              rcases hs (π g) with h0 | h1
              · exact absurd h0 hsupp
              · rw [← ofReal_norm_eq_enorm, h1]; simp
            · exact bot_le
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfin.ne
    obtain ⟨F, hFS, hFc⟩ := Set.Infinite.exists_subset_card_eq (hS : S.Infinite) n
    have := hbound F hFS
    rw [hFc] at this
    exact absurd (lt_of_le_of_lt this hn) (lt_irrefl _)

end GlobalTheory
