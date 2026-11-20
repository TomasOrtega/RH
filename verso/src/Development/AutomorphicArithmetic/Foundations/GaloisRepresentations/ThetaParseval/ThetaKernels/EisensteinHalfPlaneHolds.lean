import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHalfHoldsStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisHalfKAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisHalfK

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FFoundations%2FGaloisRepresentations%2FThetaParseval%2FThetaKernels%2FEisHalfK.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.eisenstein_half_plane_holds : _root_.SiegelEisensteinSeries.EisHalf_k := by
  first | exact @_root_.GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf_k | exact _root_.GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf_k | (intros; apply _root_.GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf_k <;> assumption)
end
