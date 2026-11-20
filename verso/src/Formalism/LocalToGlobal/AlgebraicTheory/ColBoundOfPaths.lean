import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.LogDerivativeJetsIntegral
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.JetsInOfOneVariable
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.UnitKer
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.EtPower
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.EtJets
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.TensZEt
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.TensorFourthPowerScaling
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.ScalarConst
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.DvdOfNormIntCastLt
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.ColumnBoundOfPaths
import Formalism.LocalToGlobal.AlgebraicTheory.StatementPl
import ReciprocityTheory.ReductiveGroups.LatticeEmbeddings.IotaPlace

namespace Formalism.L2.AlgTh

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem logDerJets : LogDerJets := log_derivative_jets_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem powLogDer : PowLogDer := power_log_derivative_jets
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem prodScaleJets : ProdScaleJets := product_scaling_jets
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem linScale : LinScale := linear_scaling_jets
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitKerInt : UnitKerInt := unit_kernel_integral_coords
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem etPower : EtPower := etPower_of unitKerInt
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem etJetsSigma : EtJetsSigma := etJetsSigma_of etPower logDerJets powLogDer
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem etJetsTh0 : EtJetsTh0 := etJetsTh0_of etJetsSigma
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem etThetaZ : EtThetaZ := etThetaZ_of etJetsTh0 prodScaleJets
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tensZEt : TensZEt := tensor_integral_torsion
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem etLoc : EtLoc := etLoc_of tensZEt etThetaZ linScale
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem scalarConst : ScalarConst := scalar_constant_value
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem xiSwap : XiSwap := xi_swap
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem xiEt : XiEt := xiEt_of etLoc

end Formalism.L2.AlgTh
