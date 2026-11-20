import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne

namespace UpperTheory.V.Pr

open IsLocalRing

/- English proof (translation)
Introduce `k A _ _ _ _ _ x c hx hm`. Assume the negation of the conclusion as `hne`. Establish `hy : x - algebraMap k A c ≠ 0` using `sub_ne_zero.mpr hne`. Establish `hint : IsIntegral k (x - algebraMap k A c)` using `hx.isIntegral.sub isIntegral_algebraMap`. Conclude with `(maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ hm (hint.isUnit hy))`.
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
