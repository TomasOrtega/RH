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
The claim follows from `heisenbergMul`.
-/
theorem opUMul : OpUMul := heisenbergMul
/- English proof (translation)
The claim follows from `heisenbergComm`.
-/
theorem opUComm : OpUComm := heisenbergComm
/- English proof (translation)
The claim follows from `heisenbergIsometry`.
-/
theorem opUIsom : OpUIsom := heisenbergIsometry
/- English proof (translation)
The claim follows from `precompHeisenberg`.
-/
theorem pullOpU : PullOpU := precompHeisenberg
/- English proof (translation)
The claim follows from `semicharacterBasic`.
-/
theorem semiCharBasic : SemiCharBasic := semicharacterBasic
/- English proof (translation)
The claim follows from `semicharacterHom`.
-/
theorem semiHom : SemiHom := semicharacterHom
/- English proof (translation)
The claim follows from `heisenbergAnalytic`.
-/
theorem opUAnalytic : OpUAnalytic := heisenbergAnalytic
/- English proof (translation)
The claim follows from `matrixFormBasic`.
-/
theorem matHBasic : MatHBasic := matrixFormBasic
/- English proof (translation)
The claim follows from `standardFormBasic`.
-/
theorem stdHBasic : StdHBasic := standardFormBasic
/- English proof (translation)
The claim follows from `heisenbergStandard`.
-/
theorem opUStd : OpUStd := heisenbergStandard
/- English proof (translation)
The claim follows from `heisenbergFourfold`.
-/
theorem opUBlk4 : OpUBlk4 := heisenbergFourfold

/- English proof (translation)
The claim follows from `InterClass_of semiHom`.
-/
theorem interClass : InterClass := InterClass_of semiHom
/- English proof (translation)
The claim follows from `cosetRepsExist`.
-/
theorem repsExist : RepsExist := cosetRepsExist
/- English proof (translation)
The claim follows from `InterReps_of semiHom`.
-/
theorem interReps : InterReps := InterReps_of semiHom
/- English proof (translation)
The claim follows from `InterFixed_of semiHom`.
-/
theorem interFixed : InterFixed := InterFixed_of semiHom
/- English proof (translation)
The claim follows from `InterTh_of semiHom opUAnalytic`.
-/
theorem interTh : InterTh := InterTh_of semiHom opUAnalytic
/- English proof (translation)
The claim follows from `ThIsom_of opUIsom`.
-/
theorem thIsom : ThIsom := ThIsom_of opUIsom
/- English proof (translation)
The claim follows from `characterSum`.
-/
theorem charSum : CharSum := characterSum
/- English proof (translation)
The claim follows from `IndexEq_of charSum repsExist`.
-/
theorem indexEq : IndexEq := IndexEq_of charSum repsExist
/- English proof (translation)
The claim follows from `InterInv_of opUComm interReps interFixed repsExist`.
-/
theorem interInv : InterInv := InterInv_of opUComm interReps interFixed repsExist
/- English proof (translation)
The claim follows from `LineTransport_of interInv interTh`.
-/
theorem lineTransport : LineTransport := LineTransport_of interInv interTh

/- English proof (translation)
The claim follows from `StdSelfDual_proof`.
-/
theorem stdSelfDual : StdSelfDual := StdSelfDual_proof
/- English proof (translation)
The claim follows from `StdSemiChar_proof`.
-/
theorem stdSemiChar : StdSemiChar := StdSemiChar_proof
/- English proof (translation)
The claim follows from `product_theta_mem`.
-/
theorem product_theta_mem' : ProductThetaMem := product_theta_mem
/- English proof (translation)
The claim follows from `ThStd_proof`.
-/
theorem thStd : ThStd := ThStd_proof
/- English proof (translation)
The claim follows from `fourfoldTensorMem`.
-/
theorem tens4Mem : Tens4Mem := fourfoldTensorMem
/- English proof (translation)
The claim follows from `fourth_root`.
-/
theorem fourthRoot : FourthRoot := fourth_root
/- English proof (translation)
The claim follows from `quadMultiplierSemicharacter`.
-/
theorem alphaQSemi : AlphaQSemi := quadMultiplierSemicharacter
/- English proof (translation)
The claim follows from `quadMultiplierRules`.
-/
theorem alphaQRules : AlphaQRules := quadMultiplierRules
/- English proof (translation)
The claim follows from `ThetaVector_of lineTransport thStd product_theta_mem' stdSelfDual stdSemiChar thIsom fourthRoot`.
-/
theorem thetaVector : ThetaVector :=
  ThetaVector_of lineTransport thStd product_theta_mem' stdSelfDual stdSemiChar thIsom fourthRoot

/- English proof (translation)
The claim follows from `lineUnique'`.
-/
theorem lineUnique : LineUnique := lineUnique'
/- English proof (translation)
The claim follows from `taylorLine'`.
-/
theorem taylorLine : TaylorLine := taylorLine'
/- English proof (translation)
The claim follows from `TaylorMvLinear_of lineUnique taylorLine`.
-/
theorem taylorMvLinear : TaylorMvLinear := TaylorMvLinear_of lineUnique taylorLine
/- English proof (translation)
The claim follows from `TaylorMvMul_of lineUnique taylorLine`.
-/
theorem taylorMvMul : TaylorMvMul := TaylorMvMul_of lineUnique taylorLine
/- English proof (translation)
The claim follows from `TaylorMvComp_of lineUnique taylorLine`.
-/
theorem taylorMvComp : TaylorMvComp := TaylorMvComp_of lineUnique taylorLine
/- English proof (translation)
The claim follows from `TaylorMvProd_of lineUnique taylorLine`.
-/
theorem taylorMvProd : TaylorMvProd := TaylorMvProd_of lineUnique taylorLine
/- English proof (translation)
The claim follows from `TaylorMvTens4_of lineUnique taylorLine`.
-/
theorem taylorMvTens4 : TaylorMvTens4 := TaylorMvTens4_of lineUnique taylorLine
/- English proof (translation)
The claim follows from `TaylorMvInj_of lineUnique taylorLine`.
-/
theorem taylorMvInj : TaylorMvInj := TaylorMvInj_of lineUnique taylorLine

/- English proof (translation)
The claim follows from `quadraticSemicharacters_of_productThetaMem product_theta_mem'`.
-/
theorem quadraticSemicharacter_identity_reformulated₂ : quadraticSemicharacterIdentityReformulated₂ := quadraticSemicharacters_of_productThetaMem product_theta_mem'
/- English proof (translation)
The claim follows from `quadraticSemicharacterIdentity_of_reformulated_of_taylorMv_of_repsExist_of_opUAnalytic quadraticSemicharacter_identity_reformulated₂ taylorMvLinear taylorMvComp taylorMvProd taylorMvTens4 repsExist opUAnalytic`.
-/
theorem quadraticSemicharacters_fact : quadraticSemicharacterIdentity :=
  quadraticSemicharacterIdentity_of_reformulated_of_taylorMv_of_repsExist_of_opUAnalytic quadraticSemicharacter_identity_reformulated₂ taylorMvLinear taylorMvComp taylorMvProd taylorMvTens4 repsExist opUAnalytic

end Formalism.L2.Th1.H
