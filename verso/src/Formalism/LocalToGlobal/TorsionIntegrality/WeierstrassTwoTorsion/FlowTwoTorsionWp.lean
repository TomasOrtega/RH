import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Laurent
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CompInv
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FlowBasic
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FlowTrans
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FlowTwo
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FlowThird
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CurveSer
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CurveL
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.EqWSerSubst
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.LogExp
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.ConstCurveDL
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FormalGroupEqWSeries
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.ToLTDenMulInv

universe u v

namespace Formalism.L2.Th1.A

/- English proof (translation)
The claim follows from `composition_inverse_spec`.
-/
theorem compInvSpec : CompInvSpec.{u} := composition_inverse_spec
/- English proof (translation)
The claim follows from `composition_inverse_map`.
-/
theorem compInvMap : CompInvMap.{u, v} := composition_inverse_map
/- English proof (translation)
The claim follows from `integration_spec`.
-/
theorem integSpec : IntegSpec.{u} := integration_spec

/- English proof (translation)
The claim follows from `chartFlowNegation`.
-/
theorem flowNegUW : FlowNegUW.{u} := chartFlowNegation
/- English proof (translation)
The claim follows from `chordFormula`.
-/
theorem chordRegular : ChordRegular.{u} := chordFormula
/- English proof (translation)
The claim follows from `flowTranslation`.
-/
theorem flowTranslate : FlowTranslate.{u} := flowTranslation
/- English proof (translation)
The claim follows from `flowLogDerivative`.
-/
theorem flowLogDeriv : FlowLogDeriv.{u} := flowLogDerivative
/- English proof (translation)
The claim follows from `twoTorsionTranslation`.
-/
theorem flowTwoTorsion : FlowTwoTorsion.{u} := twoTorsionTranslation
/- English proof (translation)
The claim follows from `twoTorsionTranslationWeierstrassForm`.
-/
theorem flowTwoTorsionWp : FlowTwoTorsionWp.{u} := twoTorsionTranslationWeierstrassForm

/- English proof (translation)
The claim follows from `w_series_spec`.
-/
theorem wSerSpec : WSerSpec.{u} := w_series_spec
/- English proof (translation)
The claim follows from `w_series_factorization`.
-/
theorem wSerFactor : WSerFactor.{u} := w_series_factorization
/- English proof (translation)
The claim follows from `invariant_differential_units`.
-/
theorem unitSpec : UnitSpec.{u} := invariant_differential_units
/- English proof (translation)
The claim follows from `series_map`.
-/
theorem seriesMap : SeriesMap.{u, v} := series_map
/- English proof (translation)
The claim follows from `unit_flow`.
-/
theorem flowU : FlowU.{u} := unit_flow
/- English proof (translation)
The claim follows from `invariant_derivation_spec`.
-/
theorem dLSpec : DLSpec.{u} := invariant_derivation_spec
/- English proof (translation)
The claim follows from `invariant_flow`.
-/
theorem flowL : FlowL.{u} := invariant_flow
/- English proof (translation)
The claim follows from `iSerSpec_of wSerSpec wSerFactor unitSpec flowU flowNegUW`.
-/
theorem iSerSpec : ISerSpec.{u} := iSerSpec_of wSerSpec wSerFactor unitSpec flowU flowNegUW

/- English proof (translation)
The claim follows from `logSpec_of integSpec unitSpec`.
-/
theorem logSpec : LogSpec.{u} := logSpec_of integSpec unitSpec
/- English proof (translation)
The claim follows from `expSpec_of integSpec compInvSpec unitSpec`.
-/
theorem expSpec : ExpSpec.{u} := expSpec_of integSpec compInvSpec unitSpec
/- English proof (translation)
The claim follows from `chainZ_of integSpec compInvSpec unitSpec`.
-/
theorem chainZ : ChainZ.{u} := chainZ_of integSpec compInvSpec unitSpec
/- English proof (translation)
The claim follows from `logNeg_of integSpec compInvSpec unitSpec iSerSpec`.
-/
theorem logNeg : LogNeg.{u} := logNeg_of integSpec compInvSpec unitSpec iSerSpec
/- English proof (translation)
The claim follows from `flowZ_of expSpec chainZ`.
-/
theorem flowZ : FlowZ.{u} := flowZ_of expSpec chainZ
/- English proof (translation)
The claim follows from `wpODE_of expSpec chainZ`.
-/
theorem wpODE : WpODE.{u} := wpODE_of expSpec chainZ

/- English proof (translation)
The claim follows from `formal_group_map`.
-/
theorem fglMap : FglMap.{u, v} := formal_group_map
/- English proof (translation)
The claim follows from `formal_group_chord`.
-/
theorem fglChord : FglChord.{u} := formal_group_chord
/- English proof (translation)
The claim follows from `formal_group_sum`.
-/
theorem fglSum : FglSum.{u} := formal_group_sum

/- English proof (translation)
The claim follows from `tSpec_of iSerSpec`.
-/
theorem tSpec : TSpec.{u} := tSpec_of iSerSpec
/- English proof (translation)
The claim follows from `plusChord_of flowL`.
-/
theorem plusChord : PlusChord.{u} := plusChord_of flowL
/- English proof (translation)
The claim follows from `plusFlow_of dLSpec flowL`.
-/
theorem plusFlow : PlusFlow.{u} := plusFlow_of dLSpec flowL
/- English proof (translation)
The claim follows from `plusNeg_of iSerSpec`.
-/
theorem plusNeg : PlusNeg.{u} := plusNeg_of iSerSpec
/- English proof (translation)
The claim follows from `addition_map`.
-/
theorem plusMap : PlusMap.{u, v} := addition_map

end Formalism.L2.Th1.A
