import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.LmOfLinBar
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictMod
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictAd
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictSec
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfActs

namespace PositivityTheory.KCo

/- English proof (translation)
The claim follows from `dictX_of model_existence cyclicity adjoint_statement section_statement action_uniqueness`.
-/
theorem dictionary_extended : DictX := dictX_of model_existence cyclicity adjoint_statement section_statement action_uniqueness

/- English proof (translation)
The claim follows from `dictSt_of dictionary_extended section_statement`.
-/
theorem dictionary_statement : DictSt := dictSt_of dictionary_extended section_statement

end PositivityTheory.KCo
