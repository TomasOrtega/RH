import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.CompGood
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.CompactSpaceOfIsProjOver

noncomputable section

namespace CrystallineSemistableComparison

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem comp : ModelComponents := fun l _ K _ ↦ ⟨compSm l K, compGood l K⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem geo : GeometricGenericComponents := geoMain

end CrystallineSemistableComparison
