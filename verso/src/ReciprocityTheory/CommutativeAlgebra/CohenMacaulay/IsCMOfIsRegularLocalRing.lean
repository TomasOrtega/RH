import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.RegGens

namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence

/- English proof (translation)
Establish `hd : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞)` using `(IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm`. Use `⟨inferInstance, (maximalIdeal R).spanFinrank, hd, ?_⟩` and prove the remaining obligations. Take `⟨rs, hlen, reg, hm⟩` from `ReciprocityTheory.CA.RegGens.exists_regular_gens R _ hd`. Use `⟨rs, hlen, fun r hr => ?_, reg⟩` and prove the remaining obligations. Rewrite using `[← hm]`.

Conclude with `Ideal.subset_span hr`.
-/
theorem isCM_of_isRegularLocalRing (R : Type*) [CommRing R] [IsRegularLocalRing R] : IsCM R := by
  have hd : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  refine ⟨inferInstance, (maximalIdeal R).spanFinrank, hd, ?_⟩
  obtain ⟨rs, hlen, reg, hm⟩ := ReciprocityTheory.CA.RegGens.exists_regular_gens R _ hd
  refine ⟨rs, hlen, fun r hr => ?_, reg⟩
  rw [← hm]
  exact Ideal.subset_span hr

end ReciprocityTheory.CA
