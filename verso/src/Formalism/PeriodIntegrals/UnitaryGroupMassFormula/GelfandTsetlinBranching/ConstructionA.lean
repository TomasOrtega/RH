import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFactsProofA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.FixedLineProofA

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

/- English proof (translation)
The claim follows from `extremalFacts_proof_A`.
-/
theorem extremalFacts_of (_h : PI.HwIrred) : ExtremalFacts :=
  extremalFacts_proof_A

/- English proof (translation)
The claim follows from `fixedLine_proof_A`.
-/
theorem fixed_line_exists : FixedLine :=
  fixedLine_proof_A

end PI.WGB
