import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSmulMemAdelesFiniteMultipleOfTensorCongru
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinrankSmulMemAdelesFiniteMultipleOfTensorCongru.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.finrank_smul_mem_adelesFiniteMultiple_of_tensorCongruence : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (x : AF F),
    algebraMap (AF F) (AF F ⊗[F] E) x ∈ CE F E N → Module.finrank F E • x ∈ intF F N := by
  first | exact @GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF | exact GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF | (intros; apply GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF <;> assumption)
