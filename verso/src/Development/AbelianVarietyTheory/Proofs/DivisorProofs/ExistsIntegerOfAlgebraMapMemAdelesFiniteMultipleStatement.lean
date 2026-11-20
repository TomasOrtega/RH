import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerOfAlgebraMapMemAdelesFiniteMultiple
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeExtend.exists_int_of_mem_intF` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIntegerOfAlgebraMapMemAdelesFiniteMultiple.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_integer_of_algebraMap_mem_adelesFiniteMultiple : ∀ (F : Type) [Field F] [NumberField F] (y : F) (m : ℕ), 0 < m →
    algebraMap F (AF F) y ∈ intF F m → ∃ r : 𝓞 F, y = m * r := by
  first | exact @GlobalTheory.HeckeExtend.exists_int_of_mem_intF | exact GlobalTheory.HeckeExtend.exists_int_of_mem_intF | (intros; apply GlobalTheory.HeckeExtend.exists_int_of_mem_intF <;> assumption)
