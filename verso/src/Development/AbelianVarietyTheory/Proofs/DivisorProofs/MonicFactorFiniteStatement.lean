import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LeviHC.monicFactorFinite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMonicFactorFinite.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.monicFactorFinite' : MonicFactorFinite := by
  first | exact @GlobalTheory.LeviHC.monicFactorFinite | exact GlobalTheory.LeviHC.monicFactorFinite | (intros; apply GlobalTheory.LeviHC.monicFactorFinite <;> assumption)
