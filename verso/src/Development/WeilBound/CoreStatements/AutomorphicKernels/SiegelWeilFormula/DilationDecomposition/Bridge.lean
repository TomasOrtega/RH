import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.FirstCountableGR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnIteratedDerivFamily
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StripOpenRealDiscs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountableOfNumberField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AesmIteratedDerivReal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerMulJG

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem derCont : DerCont := GlobalTheory.CompanionTheory.HolFamily.continuousOn_iteratedDeriv_family

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stripOK : StripOK := GlobalTheory.CompanionTheory.Strip.strip_open_real_discs

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matCount : MatCount := GlobalTheory.CompanionTheory.NumberFieldMatrix.matrix_countable

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem holMean : HolMean := GlobalTheory.CompanionTheory.HolMean.holomorphic_mean

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bigDense : BigDense := GlobalTheory.CompanionTheory.BigCell.dense_bigCell₂₂

end PositivityTheory.SiegelWeilFormula.Kdil

end
