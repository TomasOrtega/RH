import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorCongruenceOfSupportedAtInfinity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemTensorCongruenceOfSupportedAtInfinity.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ), 0 < N →
    ∀ w : AF F ⊗[F] E, At (evI F) w → w ∈ CE F E N := by
  first | exact @GlobalTheory.HeckeExtend.AtInf.mem_CE_of_atInf | exact GlobalTheory.HeckeExtend.AtInf.mem_CE_of_atInf | (intros; apply GlobalTheory.HeckeExtend.AtInf.mem_CE_of_atInf <;> assumption)
