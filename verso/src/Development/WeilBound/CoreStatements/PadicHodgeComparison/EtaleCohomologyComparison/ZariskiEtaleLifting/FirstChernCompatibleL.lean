import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.InWmTeichmullerSubOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubsingletonH
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.PropsC

namespace CrystallineSemistableComparison.B

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
The claim follows from `main_of (D.out l)`.
-/
theorem main : Main l := main_of (D.out l)

/- English proof (translation)
Assemble the required witnesses or components as `⟨P.cp_red, P.cp_gal, P.cp_phi, P.cp_pull, P.cp_cmp, P.cp_cup, P.cp_one, P.cp_red_fil, P.cp_smul_fil⟩`.
-/
theorem compat : Compat l :=
  ⟨P.cp_red, P.cp_gal, P.cp_phi, P.cp_pull, P.cp_cmp, P.cp_cup, P.cp_one, P.cp_red_fil, P.cp_smul_fil⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨P.ch_gal, P.ch_phi, P.ch_pull, P.ch_cup, P.ch_one, P.ch_cmp⟩`.
-/
theorem compatH : CompatH l := ⟨P.ch_gal, P.ch_phi, P.ch_pull, P.ch_cup, P.ch_one, P.ch_cmp⟩

/- English proof (translation)
The claim follows from `P.firstChern_compatible l`.
-/
theorem firstChern_compatible_l : FirstChernCompatible l := P.firstChern_compatible l

end CrystallineSemistableComparison.B
