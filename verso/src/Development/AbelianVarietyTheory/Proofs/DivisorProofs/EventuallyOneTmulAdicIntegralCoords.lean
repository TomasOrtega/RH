import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.AdicSpan

/- English proof (translation)
Establish `hfin : (⋃ i ∈ ((b.repr x).support : Set κ), HeightOneSpectrum.Support ℤ (b.repr x i)).Finite` using `(b.repr x).support.finite_toSet.biUnion fun i _ => HeightOneSpectrum.Support.finite ℤ (b.repr x i)`. Use `⟨hfin.toFinset, fun v hv i => ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]`. Distinguish the cases in `hi : b.repr x i = 0`. Rewrite using `[hi, map_zero]`.

Conclude with `zero_mem _`. Establish `h1 : v ∉ HeightOneSpectrum.Support ℤ (b.repr x i)` using `fun h => hv (hfin.mem_toFinset.2 (Set.mem_biUnion (Finsupp.mem_support_iff.2 hi) h))`. Establish `h2 : v.valuation ℚ (b.repr x i) ≤ 1` using `not_lt.1 h1`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `h3` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (b.repr x i)`.

Rewrite `h2` using `[← h3]`. Use `h2 using 2` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression.
-/
theorem exists_finset_isIntB_one_tmul (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type)
    (b : Module.Basis κ ℚ M) (x : M) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] x) := by
  have hfin : (⋃ i ∈ ((b.repr x).support : Set κ), HeightOneSpectrum.Support ℤ (b.repr x i)).Finite :=
    (b.repr x).support.finite_toSet.biUnion fun i _ => HeightOneSpectrum.Support.finite ℤ (b.repr x i)
  refine ⟨hfin.toFinset, fun v hv i => ?_⟩
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  by_cases hi : b.repr x i = 0
  · rw [hi, map_zero]; exact zero_mem _
  · have h1 : v ∉ HeightOneSpectrum.Support ℤ (b.repr x i) := fun h =>
      hv (hfin.mem_toFinset.2 (Set.mem_biUnion (Finsupp.mem_support_iff.2 hi) h))
    have h2 : v.valuation ℚ (b.repr x i) ≤ 1 := not_lt.1 h1
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h3 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (b.repr x i)
    rw [← h3] at h2
    convert h2 using 2
    rfl

end GlobalTheory.AdicSpan
