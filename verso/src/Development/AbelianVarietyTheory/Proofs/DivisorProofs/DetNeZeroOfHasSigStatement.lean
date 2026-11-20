import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfHasSig
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDetNeZeroOfHasSig.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.det_ne_zero_of_hasSig_divisor : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → M.det ≠ 0 := by
  first | exact @GlobalTheory.SigDet.det_ne_zero_of_hasSig | exact GlobalTheory.SigDet.det_ne_zero_of_hasSig | (intros; apply GlobalTheory.SigDet.det_ne_zero_of_hasSig <;> assumption)
