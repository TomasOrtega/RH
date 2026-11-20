import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LogarithmEquivalence
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Th0CharMulOpUTh0HalfPeriodEq
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlockFirstBlockEmb
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.IteratedDerivLine
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LineRestrLinSubst
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.QuadraticSemicharactersOfProductThetaMem
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.NormLtOne

namespace Formalism.L2.Th1.H

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem opUMul : OpUMul := heisenbergMul
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem opUComm : OpUComm := heisenbergComm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem opUIsom : OpUIsom := heisenbergIsometry
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pullOpU : PullOpU := precompHeisenberg
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem semiCharBasic : SemiCharBasic := semicharacterBasic
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem semiHom : SemiHom := semicharacterHom
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem opUAnalytic : OpUAnalytic := heisenbergAnalytic
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matHBasic : MatHBasic := matrixFormBasic
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stdHBasic : StdHBasic := standardFormBasic
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem opUStd : OpUStd := heisenbergStandard
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem opUBlk4 : OpUBlk4 := heisenbergFourfold

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem interClass : InterClass := InterClass_of semiHom
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem repsExist : RepsExist := cosetRepsExist
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem interReps : InterReps := InterReps_of semiHom
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem interFixed : InterFixed := InterFixed_of semiHom
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem interTh : InterTh := InterTh_of semiHom opUAnalytic
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thIsom : ThIsom := ThIsom_of opUIsom
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem charSum : CharSum := characterSum
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem indexEq : IndexEq := IndexEq_of charSum repsExist
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem interInv : InterInv := InterInv_of opUComm interReps interFixed repsExist
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lineTransport : LineTransport := LineTransport_of interInv interTh

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stdSelfDual : StdSelfDual := StdSelfDual_proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stdSemiChar : StdSemiChar := StdSemiChar_proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem product_theta_mem' : ProductThetaMem := product_theta_mem
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thStd : ThStd := ThStd_proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tens4Mem : Tens4Mem := fourfoldTensorMem
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fourthRoot : FourthRoot := fourth_root
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem alphaQSemi : AlphaQSemi := quadMultiplierSemicharacter
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem alphaQRules : AlphaQRules := quadMultiplierRules
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thetaVector : ThetaVector :=
  ThetaVector_of lineTransport thStd product_theta_mem' stdSelfDual stdSemiChar thIsom fourthRoot

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lineUnique : LineUnique := lineUnique'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem taylorLine : TaylorLine := taylorLine'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem taylorMvLinear : TaylorMvLinear := TaylorMvLinear_of lineUnique taylorLine
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem taylorMvMul : TaylorMvMul := TaylorMvMul_of lineUnique taylorLine
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem taylorMvComp : TaylorMvComp := TaylorMvComp_of lineUnique taylorLine
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem taylorMvProd : TaylorMvProd := TaylorMvProd_of lineUnique taylorLine
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem taylorMvTens4 : TaylorMvTens4 := TaylorMvTens4_of lineUnique taylorLine
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem taylorMvInj : TaylorMvInj := TaylorMvInj_of lineUnique taylorLine

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem quadraticSemicharacter_identity_reformulated₂ : quadraticSemicharacterIdentityReformulated₂ := quadraticSemicharacters_of_productThetaMem product_theta_mem'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem quadraticSemicharacters_fact : quadraticSemicharacterIdentity :=
  quadraticSemicharacterIdentity_of_reformulated_of_taylorMv_of_repsExist_of_opUAnalytic quadraticSemicharacter_identity_reformulated₂ taylorMvLinear taylorMvComp taylorMvProd taylorMvTens4 repsExist opUAnalytic

end Formalism.L2.Th1.H
