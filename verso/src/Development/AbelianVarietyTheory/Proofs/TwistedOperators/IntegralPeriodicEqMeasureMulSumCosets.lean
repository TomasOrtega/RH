import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

/- English proof (translation)
Introduce `V _ _ _ μ _ H hH hμ F ι T t hper hsupp hinj`. Use `set S : ι → Set V := fun w => (fun x => -t w + x) ⁻¹' (H : Set V) with hS`. Establish `hmem : ∀ w x, x ∈ S w ↔ x - t w ∈ H`. Introduce `w x`. Simplify using `only [hS, Set.mem_preimage, SetLike.mem_coe]`.

Rewrite using `[neg_add_eq_sub]`. Establish `hSm : ∀ w, MeasurableSet (S w)` using `fun w => (measurable_const_add (-t w)) hH`. Establish `hSμ : ∀ w, μ (S w) = μ H` using `fun w => measure_preimage_add μ (-t w) _`. Establish `hval : ∀ w x, x - t w ∈ H → F x = F (t w)`. Introduce `w x hx`.

Use `hper (t w) _ hx` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Establish `hF : F = fun x => ∑ w ∈ T, (S w).indicator (fun _ => F (t w)) x`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : ∃ w ∈ T, x - t w ∈ H`.

Take `⟨w, hw, hxw⟩` from `hx`. Rewrite using `[Finset.sum_eq_single w]`. Rewrite using `[Set.indicator_of_mem ((hmem w x).2 hxw)]`. Conclude with `hval w x hxw`. Introduce `w' hw' hne`.

Apply `Set.indicator_of_notMem` to reduce the goal to its premises. Introduce `h`. Apply `hne` to reduce the goal to its premises. Apply `hinj w' hw' w hw` to reduce the goal to its premises. Use `H.sub_mem hxw ((hmem w' x).1 h)` as an intermediate fact.

Rewrite `this` using `[sub_sub_sub_cancel_left]`. Then use the resulting hypothesis. Introduce `h`. Conclude with `absurd hw h`. Establish `h0 : F x = 0`. Assume the negation of the conclusion as `h`.

Conclude with `hx (hsupp x h)`. Rewrite using `[h0]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `w hw`.

Apply `Set.indicator_of_notMem` to reduce the goal to its premises. Introduce `h`. Conclude with `hx ⟨w, hw, (hmem w x).1 h⟩`. Establish `h1 : ∫ x, F x ∂μ = ∫ x, ∑ w ∈ T, (S w).indicator (fun _ => F (t w)) x ∂μ` using `by conv_lhs => rw [hF]`. Rewrite using `[h1, integral_finset_sum, Finset.mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w _`. Rewrite using `[integral_indicator_const _ (hSm w), Measure.real, hSμ w, Complex.real_smul]`. Both sides reduce to the same expression. Introduce `w _`.

Rewrite using `[integrable_indicator_iff (hSm w)]`. Conclude with `integrableOn_const (by rw [hSμ w]; exact hμ)`.
-/
theorem integral_periodic_eq_measure_mul_sum_cosets :
    ∀ (V : Type) [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V) [μ.IsAddLeftInvariant] (H : AddSubgroup V), MeasurableSet (H : Set V) → μ H ≠ ⊤ → ∀ (F : V → ℂ) (ι : Type) (T : Finset ι) (t : ι → V), (∀ x, ∀ h ∈ H, F (x + h) = F x) → (∀ x, F x ≠ 0 → ∃ w ∈ T, x - t w ∈ H) → (∀ w ∈ T, ∀ w' ∈ T, t w - t w' ∈ H → w = w') → ∫ x, F x ∂μ = (μ.real H : ℂ) * ∑ w ∈ T, F (t w) := by
  intro V _ _ _ μ _ H hH hμ F ι T t hper hsupp hinj
  set S : ι → Set V := fun w => (fun x => -t w + x) ⁻¹' (H : Set V) with hS
  have hmem : ∀ w x, x ∈ S w ↔ x - t w ∈ H := by
    intro w x
    simp only [hS, Set.mem_preimage, SetLike.mem_coe]
    rw [neg_add_eq_sub]
  have hSm : ∀ w, MeasurableSet (S w) := fun w => (measurable_const_add (-t w)) hH
  have hSμ : ∀ w, μ (S w) = μ H := fun w => measure_preimage_add μ (-t w) _
  have hval : ∀ w x, x - t w ∈ H → F x = F (t w) := by
    intro w x hx
    have := hper (t w) _ hx
    rwa [add_sub_cancel] at this
  have hF : F = fun x => ∑ w ∈ T, (S w).indicator (fun _ => F (t w)) x := by
    funext x
    by_cases hx : ∃ w ∈ T, x - t w ∈ H
    · obtain ⟨w, hw, hxw⟩ := hx
      rw [Finset.sum_eq_single w]
      · rw [Set.indicator_of_mem ((hmem w x).2 hxw)]
        exact hval w x hxw
      · intro w' hw' hne
        apply Set.indicator_of_notMem
        intro h
        apply hne
        apply hinj w' hw' w hw
        have := H.sub_mem hxw ((hmem w' x).1 h)
        rwa [sub_sub_sub_cancel_left] at this
      · intro h; exact absurd hw h
    · have h0 : F x = 0 := by
        by_contra h
        exact hx (hsupp x h)
      rw [h0]
      symm
      apply Finset.sum_eq_zero
      intro w hw
      apply Set.indicator_of_notMem
      intro h
      exact hx ⟨w, hw, (hmem w x).1 h⟩
  have h1 : ∫ x, F x ∂μ = ∫ x, ∑ w ∈ T, (S w).indicator (fun _ => F (t w)) x ∂μ := by
    conv_lhs => rw [hF]
  rw [h1, integral_finset_sum, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro w _
    rw [integral_indicator_const _ (hSm w), Measure.real, hSμ w, Complex.real_smul]
    rfl
  · intro w _
    rw [integrable_indicator_iff (hSm w)]
    exact integrableOn_const (by rw [hSμ w]; exact hμ)

end GlobalTheory.RootEx.UnfoldShape
