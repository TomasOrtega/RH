import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedByElementary
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSymplecticGroupGeneratedByElementary.lean&line=166#L166)
-/
theorem _root_.GlobalTheory.T.symplectic_group_generated_by_elementary : ∀ (K : Type) [Field K] [CharZero K] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix (κ ⊕ κ) (κ ⊕ κ) K),
    GlobalTheory.SympChange.IsSymp G → G ∈ Submonoid.closure (GlobalTheory.SympChange.gens (F := K) (κ := κ)) := by
  first | exact @GlobalTheory.SympChangeGen.mem_closure_gens | exact GlobalTheory.SympChangeGen.mem_closure_gens | (intros; apply GlobalTheory.SympChangeGen.mem_closure_gens <;> assumption)
