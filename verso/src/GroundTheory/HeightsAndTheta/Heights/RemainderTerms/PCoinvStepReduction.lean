import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

open Coinv

/- English proof (translation)
Introduce `K _ _ f n b k e he`. Take `⟨c, hc⟩` from `Coinv.exists_reduction (K := K) (f := f) (n := n) b k`. Use `set φ : ↥(Finset.Ioi k) → Fin f × Fin n := fun s => (b, (s : Fin n)) with hφ`. Establish `hinj : Function.Injective φ` using `fun s t h => Subtype.ext (Prod.ext_iff.mp h).2`. Choose the witnesses or unpack the hypotheses as in `⟨e₀, rfl⟩ : ∃ e₀ : Fin f × Fin n →₀ ℕ, e = e₀ + Finsupp.single (b, k) ((k : ℕ) + 1) := by`.

Use `⟨e - Finsupp.single (b, k) ((k : ℕ) + 1), ?_⟩` and prove the remaining obligations. Use extensionality with `u`. Simplify using `only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]`. Distinguish the cases in `hu : u = (b, k)`. Substitute `hu` using the available equality.

Simplify using `only [Finsupp.single_eq_same]`. Use linear arithmetic over natural numbers and integers. Simplify using `[Ne.symm hu]`. Use `set P : MvPolynomial (Fin f × Fin n) K := ∑ j ∈ range ((k : ℕ) + 1), monomial e₀ 1 * (rename φ (-c j) * X (b, k) ^ j) with hP`. Use `⟨P.support, fun e' => P.coeff e', ?_, ?_⟩` and prove the remaining obligations.

Introduce `e' he'`. Establish `h1` using `support_sum he'`. Rewrite `h1` using `[Finset.mem_biUnion]`. Take `⟨j, hj, hj'⟩` from `h1`. Establish `h2` using `support_mul _ _ hj'`.

Rewrite `h2` using `[Finset.mem_add]`. Take `⟨a, ha, d', hd', rfl⟩` from `h2`. Establish `ha' : a = e₀` using `Finset.mem_singleton.mp (support_monomial_subset ha)`. Establish `h3` using `support_mul _ _ hd'`. Rewrite `h3` using `[Finset.mem_add]`.

Take `⟨d, hd, s, hs, rfl⟩` from `h3`. Rewrite `hs` using `[X_pow_eq_monomial]`. Establish `hs' : s = Finsupp.single (b, k) j` using `Finset.mem_singleton.mp (support_monomial_subset hs)`. Rewrite `hd` using `[support_rename_of_injective hinj, Finset.mem_image]`. Take `⟨d₀, -, rfl⟩` from `hd`.

Substitute `ha' hs'` using the available equality. Establish `hoff : ∀ u : Fin f × Fin n, (u.1 ≠ b ∨ u.2 ≤ k) → Finsupp.mapDomain φ d₀ u = 0`. Introduce `u hu`. Apply `Finsupp.mapDomain_of_notMem_range` to reduce the goal to its premises. Introduce and unpack `⟨s, rfl⟩`.

Establish `hks : k < (s : Fin n)` using `Finset.mem_Ioi.mp s.2`. Break down `hu with hu | hu` into its components or cases. Conclude with `hu rfl`. Conclude with `absurd hu (not_le.mpr hks)`. Rewrite `hj` using `[Finset.mem_range]`.

Use `⟨fun u hu => ?_, ?_⟩` and prove the remaining obligations. Establish `hne : u ≠ (b, k)`. Introduce and unpack `rfl`. Apply the tactic sequence `rcases hu with h | ⟨-, h⟩ <;> exact lt_irrefl _ h`. Establish `h0` using `hoff u (by`.

Break down `hu with h | ⟨-, h⟩` into its components or cases. Conclude with `Or.inl (ne_of_lt h)`. Conclude with `Or.inr (le_of_lt h))`. Simplify using `[h0, Ne.symm hne]`. Establish `h0` using `hoff (b, k) (Or.inr le_rfl)`.

Simplify using `only [Finsupp.add_apply, h0, Finsupp.single_eq_same]`. Use linear arithmetic over natural numbers and integers. Establish `hsum : ∑ e' ∈ P.support, P.coeff e' • monomial e' (1 : K) = P` using `by conv_rhs => rw [P.as_sum]`. Use `Finset.sum_congr rfl fun e' _ => ?_` and prove the remaining obligations. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`.

Rewrite using `[hsum]`. Establish `hm : monomial (e₀ + Finsupp.single (b, k) ((k : ℕ) + 1)) (1 : K) = monomial e₀ 1 * X (b, k) ^ ((k : ℕ) + 1)`. Rewrite using `[X_pow_eq_monomial, monomial_mul, one_mul]`. Establish `hdiff : monomial (e₀ + Finsupp.single (b, k) ((k : ℕ) + 1)) (1 : K) - P = monomial e₀ 1 * (X (b, k) ^ ((k : ℕ) + 1) + ∑ j ∈ range ((k : ℕ) + 1), rename φ (c j) * X (b, k) ^ j)`. Rewrite using `[hm, hP, mul_add, Finset.mul_sum]`.

Simplify using `only [map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]`. Rewrite using `[hdiff]`. Conclude with `Ideal.mul_mem_left _ _ hc`.
-/
theorem CoinvStepReduction.proof : CoinvStepReduction.Statement := by
  classical
  intro K _ _ f n b k e he
  obtain ⟨c, hc⟩ := Coinv.exists_reduction (K := K) (f := f) (n := n) b k
  set φ : ↥(Finset.Ioi k) → Fin f × Fin n := fun s => (b, (s : Fin n)) with hφ
  have hinj : Function.Injective φ := fun s t h => Subtype.ext (Prod.ext_iff.mp h).2
  obtain ⟨e₀, rfl⟩ : ∃ e₀ : Fin f × Fin n →₀ ℕ, e = e₀ + Finsupp.single (b, k) ((k : ℕ) + 1) := by
    refine ⟨e - Finsupp.single (b, k) ((k : ℕ) + 1), ?_⟩
    ext u
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    by_cases hu : u = (b, k)
    · subst hu; simp only [Finsupp.single_eq_same]; omega
    · simp [Ne.symm hu]
  set P : MvPolynomial (Fin f × Fin n) K := ∑ j ∈ range ((k : ℕ) + 1),
      monomial e₀ 1 * (rename φ (-c j) * X (b, k) ^ j) with hP
  refine ⟨P.support, fun e' => P.coeff e', ?_, ?_⟩
  · intro e' he'
    have h1 := support_sum he'
    rw [Finset.mem_biUnion] at h1
    obtain ⟨j, hj, hj'⟩ := h1
    have h2 := support_mul _ _ hj'
    rw [Finset.mem_add] at h2
    obtain ⟨a, ha, d', hd', rfl⟩ := h2
    have ha' : a = e₀ := Finset.mem_singleton.mp (support_monomial_subset ha)
    have h3 := support_mul _ _ hd'
    rw [Finset.mem_add] at h3
    obtain ⟨d, hd, s, hs, rfl⟩ := h3
    rw [X_pow_eq_monomial] at hs
    have hs' : s = Finsupp.single (b, k) j := Finset.mem_singleton.mp (support_monomial_subset hs)
    rw [support_rename_of_injective hinj, Finset.mem_image] at hd
    obtain ⟨d₀, -, rfl⟩ := hd
    subst ha' hs'
    have hoff : ∀ u : Fin f × Fin n, (u.1 ≠ b ∨ u.2 ≤ k) → Finsupp.mapDomain φ d₀ u = 0 := by
      intro u hu
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨s, rfl⟩
      have hks : k < (s : Fin n) := Finset.mem_Ioi.mp s.2
      rcases hu with hu | hu
      · exact hu rfl
      · exact absurd hu (not_le.mpr hks)
    rw [Finset.mem_range] at hj
    refine ⟨fun u hu => ?_, ?_⟩
    · have hne : u ≠ (b, k) := by
        rintro rfl
        rcases hu with h | ⟨-, h⟩ <;> exact lt_irrefl _ h
      have h0 := hoff u (by
        rcases hu with h | ⟨-, h⟩
        · exact Or.inl (ne_of_lt h)
        · exact Or.inr (le_of_lt h))
      simp [h0, Ne.symm hne]
    · have h0 := hoff (b, k) (Or.inr le_rfl)
      simp only [Finsupp.add_apply, h0, Finsupp.single_eq_same]
      omega
  · have hsum : ∑ e' ∈ P.support, P.coeff e' • monomial e' (1 : K) = P := by
      conv_rhs => rw [P.as_sum]
      refine Finset.sum_congr rfl fun e' _ => ?_
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hsum]
    have hm : monomial (e₀ + Finsupp.single (b, k) ((k : ℕ) + 1)) (1 : K) =
        monomial e₀ 1 * X (b, k) ^ ((k : ℕ) + 1) := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    have hdiff : monomial (e₀ + Finsupp.single (b, k) ((k : ℕ) + 1)) (1 : K) - P =
        monomial e₀ 1 * (X (b, k) ^ ((k : ℕ) + 1) +
          ∑ j ∈ range ((k : ℕ) + 1), rename φ (c j) * X (b, k) ^ j) := by
      rw [hm, hP, mul_add, Finset.mul_sum]
      simp only [map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
    rw [hdiff]
    exact Ideal.mul_mem_left _ _ hc

end

end GroundTheory.Heights₂.Heights.RestTerms
