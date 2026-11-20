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
The claim follows from `log_derivative_jets_integral`.
-/
theorem logDerJets : LogDerJets := log_derivative_jets_integral
/- English proof (translation)
The claim follows from `power_log_derivative_jets`.
-/
theorem powLogDer : PowLogDer := power_log_derivative_jets
/- English proof (translation)
The claim follows from `product_scaling_jets`.
-/
theorem prodScaleJets : ProdScaleJets := product_scaling_jets
/- English proof (translation)
The claim follows from `linear_scaling_jets`.
-/
theorem linScale : LinScale := linear_scaling_jets
/- English proof (translation)
The claim follows from `unit_kernel_integral_coords`.
-/
theorem unitKerInt : UnitKerInt := unit_kernel_integral_coords
/- English proof (translation)
The claim follows from `etPower_of unitKerInt`.
-/
theorem etPower : EtPower := etPower_of unitKerInt
/- English proof (translation)
The claim follows from `etJetsSigma_of etPower logDerJets powLogDer`.
-/
theorem etJetsSigma : EtJetsSigma := etJetsSigma_of etPower logDerJets powLogDer
/- English proof (translation)
The claim follows from `etJetsTh0_of etJetsSigma`.
-/
theorem etJetsTh0 : EtJetsTh0 := etJetsTh0_of etJetsSigma
/- English proof (translation)
The claim follows from `etThetaZ_of etJetsTh0 prodScaleJets`.
-/
theorem etThetaZ : EtThetaZ := etThetaZ_of etJetsTh0 prodScaleJets
/- English proof (translation)
The claim follows from `tensor_integral_torsion`.
-/
theorem tensZEt : TensZEt := tensor_integral_torsion
/- English proof (translation)
The claim follows from `etLoc_of tensZEt etThetaZ linScale`.
-/
theorem etLoc : EtLoc := etLoc_of tensZEt etThetaZ linScale
/- English proof (translation)
The claim follows from `scalar_constant_value`.
-/
theorem scalarConst : ScalarConst := scalar_constant_value
/- English proof (translation)
The claim follows from `xi_swap`.
-/
theorem xiSwap : XiSwap := xi_swap
/- English proof (translation)
The claim follows from `xiEt_of etLoc`.
-/
theorem xiEt : XiEt := xiEt_of etLoc

end Formalism.L2.AlgTh
