import Mathlib

open NumberField Polynomial

namespace ReciprocityTheory.Cheb

/- English proof (translation)
Take `⟨p, hp⟩` from `Normal.exists_isSplittingField ℚ K`. Distinguish the cases in `h0 : p = 0`. Substitute `h0` using the available equality. Use `⟨X, X_ne_zero, ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Simplify using the standard rewrite rules. Establish `h` using `hp.adjoin_rootSet`. Simplify using `only [rootSet_zero, Algebra.adjoin_empty] at h`. Rewrite using `[eq_top_iff, ← h]`. Conclude with `bot_le`.

Conclude with `⟨p, h0, hp⟩`.
-/
theorem cxgal_exists_sf (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] :
    ∃ p : ℚ[X], p ≠ 0 ∧ IsSplittingField ℚ K p := by
  obtain ⟨p, hp⟩ := Normal.exists_isSplittingField ℚ K
  by_cases h0 : p = 0
  · subst h0
    refine ⟨X, X_ne_zero, ?_⟩
    constructor
    · simp
    · have h := hp.adjoin_rootSet
      simp only [rootSet_zero, Algebra.adjoin_empty] at h
      rw [eq_top_iff, ← h]
      exact bot_le
  · exact ⟨p, h0, hp⟩

/- English proof (translation)
Take `⟨p, hp0, hp⟩` from `cxgal_exists_sf K`. Establish `: IsSplittingField K (CyclotomicField l K) ((X ^ l - 1 : ℚ[X]).map (algebraMap ℚ K))`. Simplify using `only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one]`. Conclude with `IsCyclotomicExtension.isSplittingField_X_pow_sub_one l K (CyclotomicField l K)`. Use `IsSplittingField.mul (K := K) (L := CyclotomicField l K) p (X ^ l - 1) hp0 (X_pow_sub_C_ne_zero (NeZero.pos l) 1)` as an intermediate fact.

Establish `: Normal ℚ (CyclotomicField l K)` using `Normal.of_isSplittingField (p * (X ^ l - 1))`. Conclude with `IsGalois.mk`.
-/
theorem isGalois_cyclotomicField (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (l : ℕ) [NeZero l] :
    IsGalois ℚ (CyclotomicField l K) := by
  obtain ⟨p, hp0, hp⟩ := cxgal_exists_sf K
  have : IsSplittingField K (CyclotomicField l K) ((X ^ l - 1 : ℚ[X]).map (algebraMap ℚ K)) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one]
    exact IsCyclotomicExtension.isSplittingField_X_pow_sub_one l K (CyclotomicField l K)
  have := IsSplittingField.mul (K := K) (L := CyclotomicField l K) p (X ^ l - 1) hp0
    (X_pow_sub_C_ne_zero (NeZero.pos l) 1)
  have : Normal ℚ (CyclotomicField l K) := Normal.of_isSplittingField (p * (X ^ l - 1))
  exact IsGalois.mk

end ReciprocityTheory.Cheb
