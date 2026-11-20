import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.CoreHolds

namespace UpperTheory.Gal.KunnethLefschetz.Top
open CrystallineSemistableComparison

/- English proof (translation)
The claim follows from `core_holds.diagEt3`.
-/
theorem diagEt3_holds : CrystallineSemistableComparison.Onto.DiagEt3 := core_holds.diagEt3

/- English proof (translation)
The claim follows from `core_holds.etSide_sm l K`.
-/
theorem etSide_sm_holds (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    EtSide (Model.Sm (l := l) (K := K)) := core_holds.etSide_sm l K

/- English proof (translation)
The claim follows from `core_holds.etFin`.
-/
theorem etFin_holds : CrystallineSemistableComparison.Onto.EtFin := core_holds.etFin

end UpperTheory.Gal.KunnethLefschetz.Top
