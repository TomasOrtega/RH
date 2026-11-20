import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIntegralTensorAdeleMultiples
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsOpenIntegralTensorAdeleMultiples.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.isOpen_integralTensorAdeleMultiples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ), 0 < N →
    IsOpen (CE F E N : Set (AF F ⊗[F] E)) := by
  first | exact @GlobalTheory.HeckeExtend.CE_isOpen | exact GlobalTheory.HeckeExtend.CE_isOpen | (intros; apply GlobalTheory.HeckeExtend.CE_isOpen <;> assumption)
