import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiniteSpanKummerSelmerRepresentatives
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NoethSp
import Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteKummerSelmerOnPrimeStratum

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

/- English proof (translation)
Introduce `k K _ _ _ _ _ q _ hC`. Take `⟨n, v, hv⟩` from `UpperTheory.exists_finite_span_kummerSelmer_representatives k K q`. Set `P : Set (Fin n → k) → Prop` to `fun s => FinCls q {f | f ∈ SelAll k K q ∧ ∃ c, (f : K) = ∑ i, c i • v i ∧ c ∈ s}`. Establish `hall : P Set.univ`. Apply `UpperTheory.Et.noethSp k n P` to reduce the goal to its premises.

Use `⟨∅, ?_⟩` and prove the remaining obligations. Introduce and unpack `f ⟨_, c, _, hc⟩`. Conclude with `absurd hc (by simp)`. Introduce `s t hst ⟨T, hT⟩`. Use `⟨T, ?_⟩` and prove the remaining obligations.

Introduce and unpack `f ⟨hf, c, hfc, hc⟩`. Conclude with `hT f ⟨hf, c, hfc, hst hc⟩`. Introduce `s t ⟨T₁, h₁⟩ ⟨T₂, h₂⟩ classical`. Use `⟨T₁ ∪ T₂, ?_⟩` and prove the remaining obligations. Introduce and unpack `f ⟨hf, c, hfc, hc | hc⟩`.

Take `⟨x, hx, u, hu⟩` from `h₁ f ⟨hf, c, hfc, hc⟩`. Conclude with `⟨x, Finset.mem_union_left _ hx, u, hu⟩`. Take `⟨x, hx, u, hu⟩` from `h₂ f ⟨hf, c, hfc, hc⟩`. Conclude with `⟨x, Finset.mem_union_right _ hx, u, hu⟩`. Introduce `I hI`.

Take `⟨g, hg, T, hT⟩` from `UpperTheory.finite_kummerSelmer_on_prime_stratum k K q hC n v I hI`. Use `⟨g, hg, T, ?_⟩` and prove the remaining obligations. Introduce and unpack `f ⟨hf, c, hfc, hc₁, hc₂⟩`. Conclude with `hT f ⟨hf, c, hfc, hc₁, hc₂⟩`. Take `⟨T, hT⟩` from `hall`.

Use `⟨T, ?_⟩` and prove the remaining obligations. Introduce `f hf`. Take `⟨g, hg, ⟨c, hgc⟩, u, hfu⟩` from `hv f hf`. Take `⟨t, ht, w, hw⟩` from `hT g ⟨hg, c, hgc, Set.mem_univ c⟩`. Use `⟨t, ht, w * u, ?_⟩` and prove the remaining obligations.

Rewrite using `[hfu, hw, mul_pow, mul_assoc]`.
-/
theorem UpperTheory.finite_kummerSelmer_of_charts :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [IsFunctionField k K] (q : ℕ) [NeZero q], Charts k K q → FinCls q (SelAll k K q) := by
  intro k K _ _ _ _ _ q _ hC
  obtain ⟨n, v, hv⟩ := UpperTheory.exists_finite_span_kummerSelmer_representatives k K q
  let P : Set (Fin n → k) → Prop := fun s =>
    FinCls q {f | f ∈ SelAll k K q ∧ ∃ c, (f : K) = ∑ i, c i • v i ∧ c ∈ s}
  have hall : P Set.univ := by
    apply UpperTheory.Et.noethSp k n P
    · refine ⟨∅, ?_⟩
      rintro f ⟨_, c, _, hc⟩
      exact absurd hc (by simp)
    · intro s t hst ⟨T, hT⟩
      refine ⟨T, ?_⟩
      rintro f ⟨hf, c, hfc, hc⟩
      exact hT f ⟨hf, c, hfc, hst hc⟩
    · intro s t ⟨T₁, h₁⟩ ⟨T₂, h₂⟩
      classical
      refine ⟨T₁ ∪ T₂, ?_⟩
      rintro f ⟨hf, c, hfc, hc | hc⟩
      · obtain ⟨x, hx, u, hu⟩ := h₁ f ⟨hf, c, hfc, hc⟩
        exact ⟨x, Finset.mem_union_left _ hx, u, hu⟩
      · obtain ⟨x, hx, u, hu⟩ := h₂ f ⟨hf, c, hfc, hc⟩
        exact ⟨x, Finset.mem_union_right _ hx, u, hu⟩
    · intro I hI
      obtain ⟨g, hg, T, hT⟩ := UpperTheory.finite_kummerSelmer_on_prime_stratum k K q hC n v I hI
      refine ⟨g, hg, T, ?_⟩
      rintro f ⟨hf, c, hfc, hc₁, hc₂⟩
      exact hT f ⟨hf, c, hfc, hc₁, hc₂⟩
  obtain ⟨T, hT⟩ := hall
  refine ⟨T, ?_⟩
  intro f hf
  obtain ⟨g, hg, ⟨c, hgc⟩, u, hfu⟩ := hv f hf
  obtain ⟨t, ht, w, hw⟩ := hT g ⟨hg, c, hgc, Set.mem_univ c⟩
  refine ⟨t, ht, w * u, ?_⟩
  rw [hfu, hw, mul_pow, mul_assoc]
