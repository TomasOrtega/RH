import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory

/- English proof (translation)
Use `⟨fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[← InfinitePlace.not_isReal_iff_isComplex]`. Introduce `hw`. Establish `h` using `InfinitePlace.IsReal.comap (algebraMap E K) hw`. Conclude with `InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _) h`.
-/
theorem isTotallyComplex_of_algebra (E K : Type) [Field E] [NumberField E] [Field K]
    [NumberField K] [Algebra E K] [IsTotallyComplex E] : IsTotallyComplex K := by
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  have h := InfinitePlace.IsReal.comap (algebraMap E K) hw
  exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _) h

/- English proof (translation)
Introduce `E K _ _ _ _ _ _` and use `isTotallyComplex_of_algebra E K`.
-/
example : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsTotallyComplex E], IsTotallyComplex K :=
  fun E K _ _ _ _ _ _ => isTotallyComplex_of_algebra E K

end GlobalTheory
