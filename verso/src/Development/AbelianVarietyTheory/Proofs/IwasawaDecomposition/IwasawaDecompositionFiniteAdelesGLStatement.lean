import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFiniteAdelesGL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.BorelGL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.IwasawaFinAd.iwasawaAf | exact GlobalTheory.IwasawaFinAd.iwasawaAf | (intros; apply GlobalTheory.IwasawaFinAd.iwasawaAf <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.iwasawaDecomposition_finiteAdeles_GL : PIW.ClassFinD.IwasawaAf := by
  first | exact @GlobalTheory.IwasawaFinAd.iwasawaAf | exact GlobalTheory.IwasawaFinAd.iwasawaAf | (intros; apply GlobalTheory.IwasawaFinAd.iwasawaAf <;> assumption)
