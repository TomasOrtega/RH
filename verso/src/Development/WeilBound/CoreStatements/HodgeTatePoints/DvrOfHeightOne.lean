import Mathlib

namespace PositivityTheory.HtPt.Gc

/- English proof (translation)
Establish `hdim : ringKrullDim (Localization.AtPrime q) = 1`. Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height q, h1]`. Both sides reduce to the same expression. Establish `hnf : ¬ IsField (Localization.AtPrime q)` using `fun hf => by`. Rewrite `hdim` using `[ringKrullDim_eq_zero_of_isField hf]`.

Conclude with `zero_ne_one hdim`. Establish `hic : IsIntegrallyClosed (Localization.AtPrime q)` using `isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors`. Establish `hk : Ring.KrullDimLE 1 (Localization.AtPrime q)`. Rewrite using `[Ring.krullDimLE_iff, hdim]`. Both sides reduce to the same expression.

Establish `hD : IsDedekindDomain (Localization.AtPrime q)`. Establish `: Ring.DimensionLEOne (Localization.AtPrime q)` using `⟨fun {P} hP hP' => (Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hk) P hP hP'⟩`. Conclude with `{}`. Conclude with `((IsDiscreteValuationRing.TFAE (Localization.AtPrime q) hnf).out 0 2).2 hD`.
-/
theorem dvr_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime] (h1 : q.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  have hdim : ringKrullDim (Localization.AtPrime q) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, h1]; rfl
  have hnf : ¬ IsField (Localization.AtPrime q) := fun hf => by
    rw [ringKrullDim_eq_zero_of_isField hf] at hdim
    exact zero_ne_one hdim
  have hic : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hk : Ring.KrullDimLE 1 (Localization.AtPrime q) := by
    rw [Ring.krullDimLE_iff, hdim]; rfl
  have hD : IsDedekindDomain (Localization.AtPrime q) := by
    have : Ring.DimensionLEOne (Localization.AtPrime q) :=
      ⟨fun {P} hP hP' => (Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hk) P hP hP'⟩
    exact {}
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q) hnf).out 0 2).2 hD

end PositivityTheory.HtPt.Gc
