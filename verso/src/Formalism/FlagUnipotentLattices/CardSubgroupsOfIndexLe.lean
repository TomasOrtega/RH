import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LatticeSumBounds
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.DetMulEqSumProdMulDetSubmatrix
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IdealsOfNormEqIndexSet
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SchurAverage
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExponentInequalityNondegenerateMid
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MeasurePreservingPiCompProd
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SumComplexEmbeddingsEqSumInfinitePlace

namespace Formalism.HermitianLatticeCounting.Final.LatticeSumBounds

/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.absolute_value_bound`.
-/
theorem absA : Formalism.HermitianLatticeCounting.LatticeSumBounds.AbsA := Formalism.HermitianLatticeCounting.P.absolute_value_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.wedge_hadamard_inequality`.
-/
theorem wedgeHadamard : Formalism.HermitianLatticeCounting.LatticeSumBounds.WedgeHadamard := Formalism.HermitianLatticeCounting.P.wedge_hadamard_inequality
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.leadingMinorColumnReplace`.
-/
theorem cramerUpper : Formalism.HermitianLatticeCounting.LatticeSumBounds.CramerUpper := Formalism.HermitianLatticeCounting.P.leadingMinorColumnReplace
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.gram_hadamard_inequality`.
-/
theorem gramHadamard : Formalism.HermitianLatticeCounting.LatticeSumBounds.GramHadamard := Formalism.HermitianLatticeCounting.P.gram_hadamard_inequality
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.prodMaxInvLeSq`.
-/
theorem lemmaP : Formalism.HermitianLatticeCounting.LatticeSumBounds.LemmaP := Formalism.HermitianLatticeCounting.P.prodMaxInvLeSq
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.packing_bound`.
-/
theorem packing : Formalism.HermitianLatticeCounting.LatticeSumBounds.Packing := Formalism.HermitianLatticeCounting.P.packing_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.traceLowerBound`.
-/
theorem traceLower : Formalism.HermitianLatticeCounting.LatticeSumBounds.TraceLower := Formalism.HermitianLatticeCounting.P.traceLowerBound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.class_number_upper_bound`.
-/
theorem classNumberBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.ClassNumberBound := Formalism.HermitianLatticeCounting.P.class_number_upper_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.ideal_count_statement`.
-/
theorem c2a : Formalism.HermitianLatticeCounting.LatticeSumBounds.CardSubmodulesOfIndexLePow := Formalism.HermitianLatticeCounting.P.ideal_count_statement
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.submodule_automorphism_count`.
-/
theorem c2b : Formalism.HermitianLatticeCounting.LatticeSumBounds.CardSubmodulesAndLinearEquivBounds := Formalism.HermitianLatticeCounting.P.submodule_automorphism_count
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.unitriangularReduction`.
-/
theorem unipotentReduce : Formalism.HermitianLatticeCounting.LatticeSumBounds.UnipotentReduce := Formalism.HermitianLatticeCounting.P.unitriangularReduction
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.leadingMinorTriangularInvariant`.
-/
theorem leadingMinorInvariant : Formalism.HermitianLatticeCounting.LatticeSumBounds.LeadingMinorInvariant := Formalism.HermitianLatticeCounting.P.leadingMinorTriangularInvariant
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.normMinorMulLe`.
-/
theorem minorBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.MinorBound := Formalism.HermitianLatticeCounting.P.normMinorMulLe
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.normMinorMonomialLe`.
-/
theorem monomialMinor : Formalism.HermitianLatticeCounting.LatticeSumBounds.MonomialMinor := Formalism.HermitianLatticeCounting.P.normMinorMonomialLe
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.complementNormIdentity`.
-/
theorem omegaNorm : Formalism.HermitianLatticeCounting.LatticeSumBounds.OmegaNorm := Formalism.HermitianLatticeCounting.P.complementNormIdentity
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.box_count_alt`.
-/
theorem boxCount : Formalism.HermitianLatticeCounting.LatticeSumBounds.BoxCount := Formalism.HermitianLatticeCounting.P.box_count_alt
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.cofactorVectorKernel`.
-/
theorem kernelRowSpace : Formalism.HermitianLatticeCounting.LatticeSumBounds.KernelRowSpace := Formalism.HermitianLatticeCounting.P.cofactorVectorKernel
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.adjugateLastColumnEqCofactor`.
-/
theorem cofVecAdjugate : Formalism.HermitianLatticeCounting.LatticeSumBounds.CofVecAdjugate := Formalism.HermitianLatticeCounting.P.adjugateLastColumnEqCofactor
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.projective_quotient_card`.
-/
theorem projQuotCard : Formalism.HermitianLatticeCounting.LatticeSumBounds.ProjQuotCard := Formalism.HermitianLatticeCounting.P.projective_quotient_card
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.prodHyperbolicRatioSqLe`.
-/
theorem degFactorBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.DegFactorBound := Formalism.HermitianLatticeCounting.P.prodHyperbolicRatioSqLe
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.nondegenerateFactorBound`.
-/
theorem deNonDegBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.DeNonDegBound := Formalism.HermitianLatticeCounting.P.nondegenerateFactorBound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.degenerateFactorBound`.
-/
theorem deDegBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.DeDegBound := Formalism.HermitianLatticeCounting.P.degenerateFactorBound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.nondegenerateRowBound`.
-/
theorem nonDegRow : Formalism.HermitianLatticeCounting.LatticeSumBounds.NonDegRow := Formalism.HermitianLatticeCounting.P.nondegenerateRowBound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.degenerateRowBound`.
-/
theorem degRow : Formalism.HermitianLatticeCounting.LatticeSumBounds.DegRow := Formalism.HermitianLatticeCounting.P.degenerateRowBound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.sumNondegenerateRowsLe`.
-/
theorem nonDegSum : Formalism.HermitianLatticeCounting.LatticeSumBounds.NonDegSum := Formalism.HermitianLatticeCounting.P.sumNondegenerateRowsLe
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.sumDegenerateRowsLe`.
-/
theorem degSum : Formalism.HermitianLatticeCounting.LatticeSumBounds.DegSum := Formalism.HermitianLatticeCounting.P.sumDegenerateRowsLe
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.prodMinLeOfProdRatio`.
-/
theorem smallTerm : Formalism.HermitianLatticeCounting.LatticeSumBounds.SmallTerm := Formalism.HermitianLatticeCounting.P.prodMinLeOfProdRatio
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.singleRowBound`.
-/
theorem single_row_lattice_sum_bound : Formalism.HermitianLatticeCounting.LatticeSumBounds.SingleRowBound := Formalism.HermitianLatticeCounting.P.singleRowBound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.expSumLe'`.
-/
theorem lattice_exp_sum_upper_bound : Formalism.HermitianLatticeCounting.LatticeSumBounds.ExpSumLe' := Formalism.HermitianLatticeCounting.P.expSumLe'
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.invSqrtPowLeExp`.
-/
theorem gainSqrt : Formalism.HermitianLatticeCounting.LatticeSumBounds.GainSqrt := Formalism.HermitianLatticeCounting.P.invSqrtPowLeExp
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.box_count_big_O`.
-/
theorem boxCountO : Formalism.HermitianLatticeCounting.LatticeSumBounds.BoxCountO := Formalism.HermitianLatticeCounting.P.box_count_big_O
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.lattice_sum_alt`.
-/
theorem latticeSum : Formalism.HermitianLatticeCounting.LatticeSumBounds.LatticeSum := Formalism.HermitianLatticeCounting.P.lattice_sum_alt
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.cardCokernelRestriction`.
-/
theorem homRestrictIndex : Formalism.HermitianLatticeCounting.LatticeSumBounds.HomRestrictIndex := Formalism.HermitianLatticeCounting.P.cardCokernelRestriction

/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.coveringO_of_transference h`.
-/
theorem coveringO_of_transference (h : Formalism.HermitianLatticeCounting.LatticeSumBounds.Transference) :
    Formalism.HermitianLatticeCounting.LatticeSumBounds.CoveringO := Formalism.HermitianLatticeCounting.P.coveringO_of_transference h

end Formalism.HermitianLatticeCounting.Final.LatticeSumBounds
