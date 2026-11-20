import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce and unpack `k _ σ _ n e f h0 ⟨M, hM⟩`. Use `FormalIsogeny.isRegularLocalRing_mvPowerSeries k σ` as an intermediate fact. Use `(isRegular_of_radical_eq_maximalIdeal ?_ ?_).1` and prove the remaining obligations. Establish `h1 : Ideal.ofList (List.ofFn fun i => f (e i)) = Ideal.span (Set.range f)`. Rewrite using `[ofList_ofFn_eq_span_range]`.

Conclude with `congrArg Ideal.span (e.surjective.range_comp f)`. Rewrite using `[h1]`. Use `le_antisymm ((maximalIdeal.isMaximal _).isPrime.radical_le_iff.2 ?_) fun g hg => ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Conclude with `FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp [h0])`. Establish `h2 : MvPowerSeries.constantCoeff g = 0`. Simplify `FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg` using `[maximalIdeal_eq_bot]`. Establish `h3 : g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k))`. Rewrite using `[← germIdeal_eq_span]`.

Conclude with `h2`. Conclude with `⟨M, hM (Ideal.pow_mem_pow h3 M)⟩`. Rewrite using `[FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_field, zero_add, List.length_ofFn, ← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]`.
-/
theorem isWeaklyRegular_mvPowerSeries_of_pow_le :
    ∀ (k : Type) [Field k] (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ)
      (f : σ → MvPowerSeries σ k), (∀ j, MvPowerSeries.constantCoeff (f j) = 0) →
      (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤
        Ideal.span (Set.range f)) →
      RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries σ k) (List.ofFn fun i => f (e i)) := by
  rintro k _ σ _ n e f h0 ⟨M, hM⟩
  have := FormalIsogeny.isRegularLocalRing_mvPowerSeries k σ
  refine (isRegular_of_radical_eq_maximalIdeal ?_ ?_).1
  · have h1 : Ideal.ofList (List.ofFn fun i => f (e i)) = Ideal.span (Set.range f) := by
      rw [ofList_ofFn_eq_span_range]
      exact congrArg Ideal.span (e.surjective.range_comp f)
    rw [h1]
    refine le_antisymm ((maximalIdeal.isMaximal _).isPrime.radical_le_iff.2 ?_) fun g hg => ?_
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp [h0])
    · have h2 : MvPowerSeries.constantCoeff g = 0 := by
        simpa [maximalIdeal_eq_bot] using FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
      have h3 : g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) := by
        rw [← germIdeal_eq_span]
        exact h2
      exact ⟨M, hM (Ideal.pow_mem_pow h3 M)⟩
  · rw [FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_field, zero_add,
      List.length_ofFn, ← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

end GlobalTheory
