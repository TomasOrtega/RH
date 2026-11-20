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
A detailed English derivation is pending.
-/
theorem compInvSpec : CompInvSpec.{u} := composition_inverse_spec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem compInvMap : CompInvMap.{u, v} := composition_inverse_map
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem integSpec : IntegSpec.{u} := integration_spec

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem flowNegUW : FlowNegUW.{u} := chartFlowNegation
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem chordRegular : ChordRegular.{u} := chordFormula
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem flowTranslate : FlowTranslate.{u} := flowTranslation
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem flowLogDeriv : FlowLogDeriv.{u} := flowLogDerivative
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem flowTwoTorsion : FlowTwoTorsion.{u} := twoTorsionTranslation
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem flowTwoTorsionWp : FlowTwoTorsionWp.{u} := twoTorsionTranslationWeierstrassForm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wSerSpec : WSerSpec.{u} := w_series_spec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wSerFactor : WSerFactor.{u} := w_series_factorization
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitSpec : UnitSpec.{u} := invariant_differential_units
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem seriesMap : SeriesMap.{u, v} := series_map
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem flowU : FlowU.{u} := unit_flow
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dLSpec : DLSpec.{u} := invariant_derivation_spec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem flowL : FlowL.{u} := invariant_flow
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem iSerSpec : ISerSpec.{u} := iSerSpec_of wSerSpec wSerFactor unitSpec flowU flowNegUW

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem logSpec : LogSpec.{u} := logSpec_of integSpec unitSpec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem expSpec : ExpSpec.{u} := expSpec_of integSpec compInvSpec unitSpec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem chainZ : ChainZ.{u} := chainZ_of integSpec compInvSpec unitSpec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem logNeg : LogNeg.{u} := logNeg_of integSpec compInvSpec unitSpec iSerSpec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem flowZ : FlowZ.{u} := flowZ_of expSpec chainZ
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wpODE : WpODE.{u} := wpODE_of expSpec chainZ

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fglMap : FglMap.{u, v} := formal_group_map
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fglChord : FglChord.{u} := formal_group_chord
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fglSum : FglSum.{u} := formal_group_sum

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tSpec : TSpec.{u} := tSpec_of iSerSpec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem plusChord : PlusChord.{u} := plusChord_of flowL
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem plusFlow : PlusFlow.{u} := plusFlow_of dLSpec flowL
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem plusNeg : PlusNeg.{u} := plusNeg_of iSerSpec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem plusMap : PlusMap.{u, v} := addition_map

end Formalism.L2.Th1.A
