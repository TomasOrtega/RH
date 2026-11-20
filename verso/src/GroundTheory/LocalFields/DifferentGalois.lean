import Mathlib
import GroundTheory.LocalFields.Different
import GroundTheory.LocalFields.LowerIndexQuotient
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MinpolyProductMap

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

variable {K L} in

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.MinpolyProductMap.map_minpoly_eq_prod hx`.
-/
theorem map_minpoly_eq_prod {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    (minpoly 𝒪[K] x).map (algebraMap 𝒪[K] 𝒪[L]) =
      ∏ σ : L ≃ₐ[K] L, (X - C (integerAlgEquiv K L σ x)) :=
  _root_.UpperTheory.Reformulated.B.MinpolyProductMap.map_minpoly_eq_prod hx

variable {K L} in

/- English proof (translation)
Rewrite using `[← eval_map_algebraMap, ← derivative_map, map_minpoly_eq_prod hx, derivative_prod_finset, eval_finsetSum, Finset.sum_eq_single (1 : L ≃ₐ[K] L)]`. Rewrite using `[eval_mul, derivative_X_sub_C, eval_one, mul_one, eval_prod]`. Simplify using `only [eval_sub, eval_X, eval_C]`. Introduce `σ _ hσ`. Rewrite using `[eval_mul, eval_prod]`.

Use `mul_eq_zero_of_left (Finset.prod_eq_zero (i := 1) ?_ ?_) _` and prove the remaining obligations. Conclude with `Finset.mem_erase.mpr ⟨Ne.symm hσ, Finset.mem_univ _⟩`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem aeval_derivative_minpoly_eq_prod [DecidableEq (L ≃ₐ[K] L)] {x : 𝒪[L]}
    (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    aeval x (derivative (minpoly 𝒪[K] x)) =
      ∏ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), (x - integerAlgEquiv K L σ x) := by
  rw [← eval_map_algebraMap, ← derivative_map, map_minpoly_eq_prod hx, derivative_prod_finset,
    eval_finsetSum, Finset.sum_eq_single (1 : L ≃ₐ[K] L)]
  · rw [eval_mul, derivative_X_sub_C, eval_one, mul_one, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
  · intro σ _ hσ
    rw [eval_mul, eval_prod]
    refine mul_eq_zero_of_left (Finset.prod_eq_zero (i := 1) ?_ ?_) _
    · exact Finset.mem_erase.mpr ⟨Ne.symm hσ, Finset.mem_univ _⟩
    · simp
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Take `⟨x, hx⟩` from `exists_integer_adjoin_eq_top K L`. Rewrite using `[differentExponent_eq_addVal hx, aeval_derivative_minpoly_eq_prod hx, addVal_prod]`. Use `Finset.sum_congr rfl fun σ _ ↦ ?_` and prove the remaining obligations. Rewrite using `[lowerIndex_eq_addVal_of_adjoin_eq_top hx, ← AddValuation.map_neg, neg_sub]`.
-/
theorem differentExponent_eq_sum_lowerIndex [DecidableEq (L ≃ₐ[K] L)] :
    (differentExponent K L : ℕ∞) =
      ∑ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), lowerIndex K L σ := by
  obtain ⟨x, hx⟩ := exists_integer_adjoin_eq_top K L
  rw [differentExponent_eq_addVal hx, aeval_derivative_minpoly_eq_prod hx, addVal_prod]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [lowerIndex_eq_addVal_of_adjoin_eq_top hx, ← AddValuation.map_neg, neg_sub]

/- English proof (translation)
Establish `h` using `differentExponent_eq_sum_lowerIndex K L`. Establish `hσ : ∀ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), lowerIndex K L σ = (((Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i)).card : ℕ∞)`. Introduce `σ hσ`. Establish `hne : σ ≠ 1` using `Finset.ne_of_mem_erase hσ`. Take `⟨n, hn⟩` from `ENat.ne_top_iff_exists.mp (lowerIndex_ne_top hne)`.

Establish `hnN : n ≤ N`. Assume the negation of the conclusion as `hlt'`. Establish `hlt` using `not_le.mp hlt'`. Establish `hmem : σ ∈ lowerRamificationGroup K L N`. Rewrite using `[mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hn]`.

Conclude with `hlt` after adjusting the coercions. Rewrite `hmem` using `[hN, Subgroup.mem_bot]`. Conclude with `hne hmem`. Establish `hfilter : (Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i) = Finset.range n`. Use extensionality with `i`.

Simplify using `only [Finset.mem_filter, Finset.mem_range, mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hn, Nat.cast_le]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← hn, hfilter, Finset.card_range]`. Rewrite `h` using `[Finset.sum_congr rfl hσ]`. Establish `hswap : ∑ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), ((Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i)).card = ∑ i ∈ Finset.range N, (Nat.card (lowerRamificationGroup K L i) - 1)`.

Simplify using `only [Finset.card_filter]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← Finset.card_filter, Finset.filter_erase, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, one_mem _⟩), ← Fintype.card_subtype, Nat.card_eq_fintype_card]`. Rewrite using `[← hswap]`.

Conclude with `h` after adjusting the coercions.
-/
theorem differentExponent_eq_sum_card_lowerRamificationGroup {N : ℕ}
    (hN : lowerRamificationGroup K L N = ⊥) :
    differentExponent K L =
      ∑ i ∈ Finset.range N, (Nat.card (lowerRamificationGroup K L i) - 1) := by
  classical
  have h := differentExponent_eq_sum_lowerIndex K L
  have hσ : ∀ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), lowerIndex K L σ =
      (((Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i)).card : ℕ∞) := by
    intro σ hσ
    have hne : σ ≠ 1 := Finset.ne_of_mem_erase hσ
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (lowerIndex_ne_top hne)
    have hnN : n ≤ N := by
      by_contra hlt'
      have hlt := not_le.mp hlt'
      have hmem : σ ∈ lowerRamificationGroup K L N := by
        rw [mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hn]
        exact_mod_cast hlt
      rw [hN, Subgroup.mem_bot] at hmem
      exact hne hmem
    have hfilter : (Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i) =
        Finset.range n := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range,
        mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hn, Nat.cast_le]
      omega
    rw [← hn, hfilter, Finset.card_range]
  rw [Finset.sum_congr rfl hσ] at h
  have hswap : ∑ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L),
      ((Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i)).card =
      ∑ i ∈ Finset.range N, (Nat.card (lowerRamificationGroup K L i) - 1) := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.card_filter, Finset.filter_erase, Finset.card_erase_of_mem
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, one_mem _⟩), ← Fintype.card_subtype,
      Nat.card_eq_fintype_card]
  rw [← hswap]
  exact_mod_cast h

/- English proof (translation)
Take `⟨N, hN⟩` from `exists_lowerRamificationGroup_eq_bot K L`. Rewrite using `[differentExponent_eq_sum_card_lowerRamificationGroup K L (hN N le_rfl), finsum_eq_sum_of_support_subset _ (s := Finset.range N)]`. Introduce `i hi`. Rewrite `hi` using `[Function.mem_support]`. Rewrite using `[Finset.coe_range, Set.mem_Iio]`.

Assume the negation of the conclusion as `h'`. Establish `h` using `not_lt.mp h'`. Apply `hi` to reduce the goal to its premises. Rewrite using `[hN i (by exact_mod_cast h)]`. Simplify using the standard rewrite rules.
-/
theorem differentExponent_eq_finsum_card_lowerRamificationGroup :
    differentExponent K L = ∑ᶠ i : ℕ, (Nat.card (lowerRamificationGroup K L i) - 1) := by
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot K L
  rw [differentExponent_eq_sum_card_lowerRamificationGroup K L (hN N le_rfl),
    finsum_eq_sum_of_support_subset _ (s := Finset.range N)]
  intro i hi
  rw [Function.mem_support] at hi
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra h'
  have h := not_lt.mp h'
  apply hi
  rw [hN i (by exact_mod_cast h)]
  simp

end GroundTheory.LocalField
