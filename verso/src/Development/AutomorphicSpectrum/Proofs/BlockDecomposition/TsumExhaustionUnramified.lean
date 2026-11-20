import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps

namespace GlobalTheory.CompanionTheory.Exhaustion

open Filter Topology

variable {α E : Type*} [NormedAddCommGroup E]

/- English proof (translation)
The claim follows from `((tendsto_atTop_finset_of_monotone hC hex).eventually (eventually_ge_atTop s)).exists`.
-/
theorem exists_subset_of_exhaustion {C : ℕ → Finset α} (hC : Monotone C) (hex : ∀ a, ∃ k, a ∈ C k)
    (s : Finset α) : ∃ k, s ⊆ C k :=
  ((tendsto_atTop_finset_of_monotone hC hex).eventually (eventually_ge_atTop s)).exists

/- English proof (translation)
Use `summable_of_sum_le (c := K) (fun a => norm_nonneg _) fun s => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `exists_subset_of_exhaustion hC hex s`. Conclude with `(Finset.sum_le_sum_of_subset_of_nonneg hk fun _ _ _ => norm_nonneg _).trans (hK k)`.
-/
theorem summable_norm_of_exhaustion {f : α → E} {C : ℕ → Finset α} (hC : Monotone C)
    (hex : ∀ a, ∃ k, a ∈ C k) {K : ℝ} (hK : ∀ k, ∑ a ∈ C k, ‖f a‖ ≤ K) :
    Summable fun a => ‖f a‖ := by
  refine summable_of_sum_le (c := K) (fun a => norm_nonneg _) fun s => ?_
  obtain ⟨k, hk⟩ := exists_subset_of_exhaustion hC hex s
  exact (Finset.sum_le_sum_of_subset_of_nonneg hk fun _ _ _ => norm_nonneg _).trans (hK k)

/- English proof (translation)
Establish `hs : Summable f` using `(summable_norm_of_exhaustion hC hex hK).of_norm`. Conclude with `⟨hs, hs.hasSum.comp (tendsto_atTop_finset_of_monotone hC hex)⟩`.
-/
theorem tsum_exhaust [CompleteSpace E] {f : α → E} {C : ℕ → Finset α} (hC : Monotone C)
    (hex : ∀ a, ∃ k, a ∈ C k) {K : ℝ} (hK : ∀ k, ∑ a ∈ C k, ‖f a‖ ≤ K) :
    Summable f ∧ Tendsto (fun k => ∑ a ∈ C k, f a) atTop (𝓝 (∑' a, f a)) := by
  have hs : Summable f := (summable_norm_of_exhaustion hC hex hK).of_norm
  exact ⟨hs, hs.hasSum.comp (tendsto_atTop_finset_of_monotone hC hex)⟩

/- English proof (translation)
Introduce `α f C hC hex ⟨K, hK⟩`. Conclude with `⟨summable_norm_of_exhaustion hC hex hK, (tsum_exhaust hC hex hK).2⟩`.
-/
theorem tsum_exhaust_prop : PositivityTheory.SiegelWeilFormula.Gunr.TsumExhaust := by
  intro α f C hC hex ⟨K, hK⟩
  exact ⟨summable_norm_of_exhaustion hC hex hK, (tsum_exhaust hC hex hK).2⟩

end GlobalTheory.CompanionTheory.Exhaustion
