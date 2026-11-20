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
/- English proof (citation)
Apply `GlobalTheory.IwasawaFinAd.iwasawaAf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIwasawaDecompositionFiniteAdelesGL.lean&line=135#L135)
-/
theorem _root_.GlobalTheory.T.iwasawaDecomposition_finiteAdeles_GL : PIW.ClassFinD.IwasawaAf := by
  first | exact @GlobalTheory.IwasawaFinAd.iwasawaAf | exact GlobalTheory.IwasawaFinAd.iwasawaAf | (intros; apply GlobalTheory.IwasawaFinAd.iwasawaAf <;> assumption)
