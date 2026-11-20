import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne

namespace UpperTheory.V.Pr

open IsLocalRing

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem constOfAlg : ConstOfAlg := by
  intro k A _ _ _ _ _ x c hx hm
  by_contra hne
  have hy : x - algebraMap k A c ≠ 0 := sub_ne_zero.mpr hne
  have hint : IsIntegral k (x - algebraMap k A c) :=
    hx.isIntegral.sub isIntegral_algebraMap
  exact (maximalIdeal.isMaximal A).ne_top
    (Ideal.eq_top_of_isUnit_mem _ hm (hint.isUnit hy))

end UpperTheory.V.Pr
