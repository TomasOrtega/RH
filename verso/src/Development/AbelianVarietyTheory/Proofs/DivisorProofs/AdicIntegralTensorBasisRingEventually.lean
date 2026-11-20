import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

/- English proof (translation)
Introduce `A _ _ _ κ b`. Use `haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b`. Establish `hc : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ × κ, algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b t.1 * b t.2.1) t.2.2) ∈ v.adicCompletionIntegers ℚ` using `Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _`. Establish `h1 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ k : κ, algebraMap ℚ (v.adicCompletion ℚ) (b.repr 1 k) ∈ v.adicCompletionIntegers ℚ` using `Filter.eventually_all.2 fun k => rat_mem_adicCompletionIntegers_eventually _`. Establish `hfin` using `Filter.eventually_cofinite.1 (hc.and h1)`.

Use `⟨hfin.toFinset, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite `hv` using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not]`. Take `⟨hcv, h1v⟩` from `hv`. Use `⟨fun k => ?_, fun y z hy hz k => ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.one_def, repr_tmul_apply, one_mul]`.

Conclude with `h1v k`. Rewrite using `[eq_sum_tmul b v y, eq_sum_tmul b v z, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum, Finsupp.finset_sum_apply]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply]`. Conclude with `mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))`.
-/
theorem isIntB_one_mul_eventually : ∀ (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (κ : Type)
    (b : Module.Basis κ ℚ A),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b 1 ∧
      ∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z) := by
  intro A _ _ _ κ b
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hc : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b t.1 * b t.2.1) t.2.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have h1 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ k : κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr 1 k) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun k => rat_mem_adicCompletionIntegers_eventually _
  have hfin := Filter.eventually_cofinite.1 (hc.and h1)
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  obtain ⟨hcv, h1v⟩ := hv
  refine ⟨fun k => ?_, fun y z hy hz k => ?_⟩
  · rw [Algebra.TensorProduct.one_def, repr_tmul_apply, one_mul]
    exact h1v k
  · rw [eq_sum_tmul b v y, eq_sum_tmul b v z, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun i _ => ?_
    rw [map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply]
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))

end GlobalTheory.AdicSpan
