import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.InWmTeichmullerSubOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubsingletonH
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.PropsC

namespace CrystallineSemistableComparison.B

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem main : Main l := main_of (D.out l)

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem compat : Compat l :=
  ⟨P.cp_red, P.cp_gal, P.cp_phi, P.cp_pull, P.cp_cmp, P.cp_cup, P.cp_one, P.cp_red_fil, P.cp_smul_fil⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem compatH : CompatH l := ⟨P.ch_gal, P.ch_phi, P.ch_pull, P.ch_cup, P.ch_one, P.ch_cmp⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem firstChern_compatible_l : FirstChernCompatible l := P.firstChern_compatible l

end CrystallineSemistableComparison.B
