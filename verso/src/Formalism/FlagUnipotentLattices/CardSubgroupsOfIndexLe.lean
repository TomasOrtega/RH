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
A detailed English derivation is pending.
-/
theorem absA : Formalism.HermitianLatticeCounting.LatticeSumBounds.AbsA := Formalism.HermitianLatticeCounting.P.absolute_value_bound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wedgeHadamard : Formalism.HermitianLatticeCounting.LatticeSumBounds.WedgeHadamard := Formalism.HermitianLatticeCounting.P.wedge_hadamard_inequality
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cramerUpper : Formalism.HermitianLatticeCounting.LatticeSumBounds.CramerUpper := Formalism.HermitianLatticeCounting.P.leadingMinorColumnReplace
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gramHadamard : Formalism.HermitianLatticeCounting.LatticeSumBounds.GramHadamard := Formalism.HermitianLatticeCounting.P.gram_hadamard_inequality
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemmaP : Formalism.HermitianLatticeCounting.LatticeSumBounds.LemmaP := Formalism.HermitianLatticeCounting.P.prodMaxInvLeSq
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem packing : Formalism.HermitianLatticeCounting.LatticeSumBounds.Packing := Formalism.HermitianLatticeCounting.P.packing_bound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem traceLower : Formalism.HermitianLatticeCounting.LatticeSumBounds.TraceLower := Formalism.HermitianLatticeCounting.P.traceLowerBound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem classNumberBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.ClassNumberBound := Formalism.HermitianLatticeCounting.P.class_number_upper_bound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem c2a : Formalism.HermitianLatticeCounting.LatticeSumBounds.CardSubmodulesOfIndexLePow := Formalism.HermitianLatticeCounting.P.ideal_count_statement
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem c2b : Formalism.HermitianLatticeCounting.LatticeSumBounds.CardSubmodulesAndLinearEquivBounds := Formalism.HermitianLatticeCounting.P.submodule_automorphism_count
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unipotentReduce : Formalism.HermitianLatticeCounting.LatticeSumBounds.UnipotentReduce := Formalism.HermitianLatticeCounting.P.unitriangularReduction
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem leadingMinorInvariant : Formalism.HermitianLatticeCounting.LatticeSumBounds.LeadingMinorInvariant := Formalism.HermitianLatticeCounting.P.leadingMinorTriangularInvariant
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem minorBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.MinorBound := Formalism.HermitianLatticeCounting.P.normMinorMulLe
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem monomialMinor : Formalism.HermitianLatticeCounting.LatticeSumBounds.MonomialMinor := Formalism.HermitianLatticeCounting.P.normMinorMonomialLe
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem omegaNorm : Formalism.HermitianLatticeCounting.LatticeSumBounds.OmegaNorm := Formalism.HermitianLatticeCounting.P.complementNormIdentity
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem boxCount : Formalism.HermitianLatticeCounting.LatticeSumBounds.BoxCount := Formalism.HermitianLatticeCounting.P.box_count_alt
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernelRowSpace : Formalism.HermitianLatticeCounting.LatticeSumBounds.KernelRowSpace := Formalism.HermitianLatticeCounting.P.cofactorVectorKernel
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cofVecAdjugate : Formalism.HermitianLatticeCounting.LatticeSumBounds.CofVecAdjugate := Formalism.HermitianLatticeCounting.P.adjugateLastColumnEqCofactor
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem projQuotCard : Formalism.HermitianLatticeCounting.LatticeSumBounds.ProjQuotCard := Formalism.HermitianLatticeCounting.P.projective_quotient_card
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem degFactorBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.DegFactorBound := Formalism.HermitianLatticeCounting.P.prodHyperbolicRatioSqLe
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem deNonDegBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.DeNonDegBound := Formalism.HermitianLatticeCounting.P.nondegenerateFactorBound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem deDegBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.DeDegBound := Formalism.HermitianLatticeCounting.P.degenerateFactorBound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nonDegRow : Formalism.HermitianLatticeCounting.LatticeSumBounds.NonDegRow := Formalism.HermitianLatticeCounting.P.nondegenerateRowBound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem degRow : Formalism.HermitianLatticeCounting.LatticeSumBounds.DegRow := Formalism.HermitianLatticeCounting.P.degenerateRowBound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nonDegSum : Formalism.HermitianLatticeCounting.LatticeSumBounds.NonDegSum := Formalism.HermitianLatticeCounting.P.sumNondegenerateRowsLe
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem degSum : Formalism.HermitianLatticeCounting.LatticeSumBounds.DegSum := Formalism.HermitianLatticeCounting.P.sumDegenerateRowsLe
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem smallTerm : Formalism.HermitianLatticeCounting.LatticeSumBounds.SmallTerm := Formalism.HermitianLatticeCounting.P.prodMinLeOfProdRatio
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem single_row_lattice_sum_bound : Formalism.HermitianLatticeCounting.LatticeSumBounds.SingleRowBound := Formalism.HermitianLatticeCounting.P.singleRowBound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lattice_exp_sum_upper_bound : Formalism.HermitianLatticeCounting.LatticeSumBounds.ExpSumLe' := Formalism.HermitianLatticeCounting.P.expSumLe'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gainSqrt : Formalism.HermitianLatticeCounting.LatticeSumBounds.GainSqrt := Formalism.HermitianLatticeCounting.P.invSqrtPowLeExp
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem boxCountO : Formalism.HermitianLatticeCounting.LatticeSumBounds.BoxCountO := Formalism.HermitianLatticeCounting.P.box_count_big_O
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem latticeSum : Formalism.HermitianLatticeCounting.LatticeSumBounds.LatticeSum := Formalism.HermitianLatticeCounting.P.lattice_sum_alt
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem homRestrictIndex : Formalism.HermitianLatticeCounting.LatticeSumBounds.HomRestrictIndex := Formalism.HermitianLatticeCounting.P.cardCokernelRestriction

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem coveringO_of_transference (h : Formalism.HermitianLatticeCounting.LatticeSumBounds.Transference) :
    Formalism.HermitianLatticeCounting.LatticeSumBounds.CoveringO := Formalism.HermitianLatticeCounting.P.coveringO_of_transference h

end Formalism.HermitianLatticeCounting.Final.LatticeSumBounds
