import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsAdelicSchwartzNeZeroAtOrigin.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ φ ∈ schA F κ, φ 0 ≠ 0 := by
  first | exact @GlobalTheory.SchANonzero.exists_mem_schA_ne_zero | exact GlobalTheory.SchANonzero.exists_mem_schA_ne_zero | (intros; apply GlobalTheory.SchANonzero.exists_mem_schA_ne_zero <;> assumption)
