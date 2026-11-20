import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.WeilBound.CoreStatements.IdealCycleValues.ProdMapToMultiset
import Development.WeilBound.CoreStatements.IdealCycleValues.IntersectionNumbersPermInvariant

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

/- English proof (translation)
Introduce `O _ _ _ K _ _ ι _ σ Z cls H G Q`. Establish `key : ∀ (P : MvPolynomial σ ℝ) (L : List (K → ℤ)) (s : Finset (σ →₀ ℕ)), P.support ⊆ s → cycNum Z cls P L = ∑ κ ∈ s, MvPolynomial.coeff κ P * (cycList Z (classList cls κ ++ L) : ℝ)`. Introduce `P L s hs`. Use `show ∑ κ ∈ P.support, MvPolynomial.coeff κ P * (cycList Z (classList cls κ ++ L) : ℝ) = _`. Use `Finset.sum_subset hs (fun κ _ hκ => ?_)` and prove the remaining obligations.

Rewrite using `[MvPolynomial.notMem_support_iff.mp hκ, zero_mul]`. Establish `hadd : ∀ P P' : MvPolynomial σ ℝ, cycNum Z cls (P + P') Q = cycNum Z cls P Q + cycNum Z cls P' Q`. Introduce `P P'`. Rewrite using `[key (P + P') Q (P.support ∪ P'.support) MvPolynomial.support_add, key P Q (P.support ∪ P'.support) Finset.subset_union_left, key P' Q (P.support ∪ P'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun _ _ => ?_)` and prove the remaining obligations.

Rewrite using `[MvPolynomial.coeff_add, add_mul]`. Establish `hzero : cycNum Z cls (0 : MvPolynomial σ ℝ) Q = 0`. Rewrite using `[key 0 Q ∅ (by simp)]`. Simplify using the standard rewrite rules. Establish `hsum : ∀ (α : Type) (s : Finset α) (P : α → MvPolynomial σ ℝ), cycNum Z cls (∑ a ∈ s, P a) Q = ∑ a ∈ s, cycNum Z cls (P a) Q`.

Introduce `α s P`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hzero]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]`. Establish `hmon : ∀ (κ : σ →₀ ℕ) (c : ℝ), cycNum Z cls (monomial κ c) Q = c * (cycList Z (classList cls κ ++ Q) : ℝ)`.

Introduce `κ c`. Rewrite using `[key _ Q {κ} MvPolynomial.support_monomial_subset, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]`. Establish `hperm : ∀ ν μ : σ →₀ ℕ, cycList Z (classList cls (ν + μ) ++ Q) = cycList Z (classList cls ν ++ (classList cls μ ++ Q))`. Introduce `ν μ`. Establish `hp : (classList cls (ν + μ)).Perm (classList cls ν ++ classList cls μ)`.

Rewrite using `[← Multiset.coe_eq_coe, ← Multiset.coe_add]`. Simplify using `only [classList, Multiset.coe_toList, Finsupp.toMultiset_add, Multiset.map_add]`. Rewrite using `[← List.append_assoc]`. Conclude with `BaseChangeColon.intersection_numbers_perm_invariant.2 O K ι Z _ _ (hp.append_right Q)`. Use `conv_lhs => rw [H.as_sum, G.as_sum, Finset.sum_mul_sum]`.

Rewrite using `[hsum]`. Repeatedly rewrite using `[hsum, MvPolynomial.monomial_mul, hmon]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun μ _ => ?_)` and prove the remaining obligations. Rewrite using `[key H (classList cls μ ++ Q) H.support subset_rfl, Finset.mul_sum]`.

Use `Finset.sum_congr rfl (fun ν _ => ?_)` and prove the remaining obligations. Rewrite using `[hperm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem BaseChangeColon.cycNum_mul_expansion : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (Z : Ideal (MRing ι O) → ℤ) (cls : σ → K → ℤ) (H G : MvPolynomial σ ℝ) (Q : List (K → ℤ)), cycNum Z cls (H * G) Q = ∑ μ ∈ G.support, G.coeff μ * cycNum Z cls H (classList cls μ ++ Q) := by
  intro O _ _ _ K _ _ ι _ σ Z cls H G Q
  classical
  have key : ∀ (P : MvPolynomial σ ℝ) (L : List (K → ℤ)) (s : Finset (σ →₀ ℕ)), P.support ⊆ s →
      cycNum Z cls P L = ∑ κ ∈ s, MvPolynomial.coeff κ P * (cycList Z (classList cls κ ++ L) : ℝ) := by
    intro P L s hs
    show ∑ κ ∈ P.support, MvPolynomial.coeff κ P * (cycList Z (classList cls κ ++ L) : ℝ) = _
    refine Finset.sum_subset hs (fun κ _ hκ => ?_)
    rw [MvPolynomial.notMem_support_iff.mp hκ, zero_mul]
  have hadd : ∀ P P' : MvPolynomial σ ℝ, cycNum Z cls (P + P') Q = cycNum Z cls P Q + cycNum Z cls P' Q := by
    intro P P'
    rw [key (P + P') Q (P.support ∪ P'.support) MvPolynomial.support_add,
      key P Q (P.support ∪ P'.support) Finset.subset_union_left,
      key P' Q (P.support ∪ P'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_add, add_mul]
  have hzero : cycNum Z cls (0 : MvPolynomial σ ℝ) Q = 0 := by
    rw [key 0 Q ∅ (by simp)]
    simp
  have hsum : ∀ (α : Type) (s : Finset α) (P : α → MvPolynomial σ ℝ),
      cycNum Z cls (∑ a ∈ s, P a) Q = ∑ a ∈ s, cycNum Z cls (P a) Q := by
    intro α s P
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  have hmon : ∀ (κ : σ →₀ ℕ) (c : ℝ), cycNum Z cls (monomial κ c) Q = c * (cycList Z (classList cls κ ++ Q) : ℝ) := by
    intro κ c
    rw [key _ Q {κ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]
  have hperm : ∀ ν μ : σ →₀ ℕ, cycList Z (classList cls (ν + μ) ++ Q) = cycList Z (classList cls ν ++ (classList cls μ ++ Q)) := by
    intro ν μ
    have hp : (classList cls (ν + μ)).Perm (classList cls ν ++ classList cls μ) := by
      rw [← Multiset.coe_eq_coe, ← Multiset.coe_add]
      simp only [classList, Multiset.coe_toList, Finsupp.toMultiset_add, Multiset.map_add]
    rw [← List.append_assoc]
    exact BaseChangeColon.intersection_numbers_perm_invariant.2 O K ι Z _ _ (hp.append_right Q)
  conv_lhs => rw [H.as_sum, G.as_sum, Finset.sum_mul_sum]
  rw [hsum]
  simp_rw [hsum, MvPolynomial.monomial_mul, hmon]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [key H (classList cls μ ++ Q) H.support subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [hperm]
  ring
