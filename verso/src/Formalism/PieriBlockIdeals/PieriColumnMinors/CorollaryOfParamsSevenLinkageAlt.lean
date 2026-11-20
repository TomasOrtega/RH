import Formalism.PieriBlockIdeals.StatementTop
import Formalism.PieriBlockIdeals.PieriColumnMinors.CorollaryOfParamsSevenLinkage
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PrimeCount

namespace Formalism.CohomologicalDescent.Top

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem prime_count_bound_rs : Formalism.CohomologicalDescent.LogSmallConstantBounds.PrimeCountingBound := prime_count_bound

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem inclusion_w_seven_real_holds : HidaLatticeInclusionAtCoarseWeightBound := Formalism.CohomologicalDescent.Down7.inclusion_w_seven_real_holds

/- English proof (translation)
Supply the required witnesses or components.
-/
example : ∃ B : Prop, Formalism.CohomologicalDescent.Down7.CorollaryOfRecord7 = (Formalism.CohomologicalDescent.LA.LemmaAZ → Formalism.CohomologicalDescent.LogSmallConstantBounds.PrimeCountingBound → B) ∧
    Formalism.CohomologicalDescent.Top.CorollaryOfRecord7 = (Formalism.CohomologicalDescent.LA.LemmaAZ → B) := ⟨_, rfl, rfl⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
example : ∃ B : Prop, Formalism.CohomologicalDescent.Down7.CorollaryOfRecord7Link = (Formalism.CohomologicalDescent.LA.LemmaAZ → Formalism.CohomologicalDescent.LogSmallConstantBounds.PrimeCountingBound → B) ∧
    Formalism.CohomologicalDescent.Top.CorollaryOfRecord7Link = (Formalism.CohomologicalDescent.LA.LemmaAZ → B) := ⟨_, rfl, rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
example : Formalism.CohomologicalDescent.Top.HidaLatticeInclusionAtCoarseWeightBound = Formalism.CohomologicalDescent.Down7.HidaLatticeInclusionAtCoarseWeightBound := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
example : Formalism.CohomologicalDescent.Top.RecIncl7 = Formalism.CohomologicalDescent.Down7.RecIncl7 := rfl

end Formalism.CohomologicalDescent.Top
