import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core

/- English proof (translation)
Introduce `V _ _ _ χ μ h L _ hLo a y`. Take `⟨hTG, _, _, hSC, hB, hH, _, _, _, _, _, hadd, _⟩` from `h`. Establish `hLm : MeasurableSet (L : Set V)` using `hLo.measurableSet`. Establish `key : ∫ x, Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y ∂μ = ((μ L).toReal : ℂ) * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y`. Distinguish the cases in `hy : y ∈ perp χ L`.

Establish `h1 : (fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) = fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x ∈ (L : Set V)`. Simplify using `[Set.indicator_of_mem hx, hy x hx]`. Simplify using `[Set.indicator_of_notMem hx]`.

Rewrite using `[h1, integral_indicator_const _ hLm, Set.indicator_of_mem hy]`. Simplify using `[Measure.real]`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl, hne⟩ : ∃ l ∈ (L : Set V), χ l y ≠ 1 := by`. Simplify `hy` using `[perp]`. Use `set J := ∫ x, Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y ∂μ with hJ`.

Establish `hshift : J = χ l y * J`. Establish `h2` using `integral_add_right_eq_self (μ := μ) (fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) l`. Use `h2.symm.trans ?_` and prove the remaining obligations. Rewrite using `[hJ, ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations.

Establish `hmem : x + l ∈ (L : Set V) ↔ x ∈ (L : Set V)` using `L.add_mem_cancel_right hl`. Distinguish the cases in `hx : x ∈ (L : Set V)`. Simplify using `only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx), hadd]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]`.

Establish `hJ0 : J = 0`. Establish `h3 : (1 - χ l y) * J = 0`. Rewrite using `[sub_mul, one_mul, ← hshift, sub_self]`. Break down `mul_eq_zero.1 h3 with h4 | h4` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h4).symm hne`.

Conclude with `h4`. Rewrite using `[hJ0, Set.indicator_of_notMem hy, mul_zero]`. Unfold `fou`. Establish `h5` using `integral_add_right_eq_self (μ := μ) (fun x => Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ)) x * χ x y) a`. Rewrite using `[← h5]`.

Establish `h6 : (fun x => Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ)) (x + a) * χ (x + a) y) = fun x => χ a y * (Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y)`. Use function extensionality and compare the values at `x`. Establish `hmem : x + a ∈ {x | x - a ∈ L} ↔ x ∈ (L : Set V)` using `by simp`. Distinguish the cases in `hx : x ∈ (L : Set V)`. Simplify using `only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx), hadd]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]`. Rewrite using `[h6, integral_const_mul, key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fou_indicator_coset :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V),
      NADual V χ μ → ∀ L : AddSubgroup V, IsCompact (L : Set V) → IsOpen (L : Set V) → ∀ a y : V,
        fou χ μ (Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ))) y =
          ((μ L).toReal : ℂ) * χ a y * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
  intro V _ _ _ χ μ h L _ hLo a y
  obtain ⟨hTG, _, _, hSC, hB, hH, _, _, _, _, _, hadd, _⟩ := h
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet

  have key : ∫ x, Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y ∂μ =
      ((μ L).toReal : ℂ) * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
    by_cases hy : y ∈ perp χ L
    · have h1 : (fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) =
          fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x := by
        funext x
        by_cases hx : x ∈ (L : Set V)
        · simp [Set.indicator_of_mem hx, hy x hx]
        · simp [Set.indicator_of_notMem hx]
      rw [h1, integral_indicator_const _ hLm, Set.indicator_of_mem hy]
      simp [Measure.real]
    · obtain ⟨l, hl, hne⟩ : ∃ l ∈ (L : Set V), χ l y ≠ 1 := by
        simpa [perp] using hy
      set J := ∫ x, Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y ∂μ with hJ
      have hshift : J = χ l y * J := by
        have h2 := integral_add_right_eq_self (μ := μ)
          (fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) l
        refine h2.symm.trans ?_
        rw [hJ, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have hmem : x + l ∈ (L : Set V) ↔ x ∈ (L : Set V) := L.add_mem_cancel_right hl
        by_cases hx : x ∈ (L : Set V)
        · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx), hadd]
          ring
        · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
      have hJ0 : J = 0 := by
        have h3 : (1 - χ l y) * J = 0 := by
          rw [sub_mul, one_mul, ← hshift, sub_self]
        rcases mul_eq_zero.1 h3 with h4 | h4
        · exact absurd (sub_eq_zero.1 h4).symm hne
        · exact h4
      rw [hJ0, Set.indicator_of_notMem hy, mul_zero]

  unfold fou
  have h5 := integral_add_right_eq_self (μ := μ)
    (fun x => Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ)) x * χ x y) a
  rw [← h5]
  have h6 : (fun x => Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ)) (x + a) * χ (x + a) y) =
      fun x => χ a y * (Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) := by
    funext x
    have hmem : x + a ∈ {x | x - a ∈ L} ↔ x ∈ (L : Set V) := by simp
    by_cases hx : x ∈ (L : Set V)
    · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx), hadd]
      ring
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
  rw [h6, integral_const_mul, key]
  ring

end GlobalTheory.CompanionTheory.SW.Core
