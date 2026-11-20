import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.CompGood
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.CompactSpaceOfIsProjOver

noncomputable section

namespace CrystallineSemistableComparison

/- English proof (translation)
The claim follows from `fun l _ K _ ↦ ⟨compSm l K, compGood l K⟩`.
-/
theorem comp : ModelComponents := fun l _ K _ ↦ ⟨compSm l K, compGood l K⟩

/- English proof (translation)
The claim follows from `geoMain`.
-/
theorem geo : GeometricGenericComponents := geoMain

end CrystallineSemistableComparison
