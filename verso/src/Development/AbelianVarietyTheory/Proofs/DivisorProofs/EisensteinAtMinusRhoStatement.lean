import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinAtMinusRho
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEisensteinAtMinusRho.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.eisenstein_at_minus_rho : GlobalTheory.ThK.KP → GlobalTheory.ConeSmall.EisAtMinusRho := by
  first | exact @GlobalTheory.ConeSmall.eisAtMinusRho | exact GlobalTheory.ConeSmall.eisAtMinusRho | (intros; apply GlobalTheory.ConeSmall.eisAtMinusRho <;> assumption)
