import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.DensEqOfBase
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchTop

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

/- English proof (translation)
The claim follows from `densEq_of_base PositivityTheory.PfSWUS.SchInf.schwartzDensInf hBase hO`.
-/
theorem densEq_of_one (hBase : BaseOne) (hO : MassOne) : PositivityTheory.SiegelWeilFormula.Gen.DensEq :=
  densEq_of_base PositivityTheory.PfSWUS.SchInf.schwartzDensInf hBase hO

end PositivityTheory.SiegelWeilFormula.Densx

end
