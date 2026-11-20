import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem isTotallyComplex_of_algebra (E K : Type) [Field E] [NumberField E] [Field K]
    [NumberField K] [Algebra E K] [IsTotallyComplex E] : IsTotallyComplex K := by
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  have h := InfinitePlace.IsReal.comap (algebraMap E K) hw
  exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _) h

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
example : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsTotallyComplex E], IsTotallyComplex K :=
  fun E K _ _ _ _ _ _ => isTotallyComplex_of_algebra E K

end GlobalTheory
