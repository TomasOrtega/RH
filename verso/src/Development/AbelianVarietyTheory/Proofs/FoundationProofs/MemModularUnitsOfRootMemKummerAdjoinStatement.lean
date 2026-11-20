import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularUnitsOfRootMemKummerAdjoin
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FMemModularUnitsOfRootMemKummerAdjoin.lean&line=166#L166)
-/
theorem _root_.GlobalTheory.T.mem_modularUnits_of_root_mem_kummer_adjoin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (m l : ℕ), 0 < m → 0 < l → ∀ (θ : AlgebraicClosure X.K) (f : X.Kˣ), θ ∈ IntermediateField.adjoin X.K {y : AlgebraicClosure X.K | ∃ U ∈ X.Un m, y ^ m = algebraMap X.K (AlgebraicClosure X.K) (U : X.K)} → θ ^ l = algebraMap X.K (AlgebraicClosure X.K) (f : X.K) → f ∈ X.Un l := by
  first | exact @GlobalTheory.KZ.UnRoot.mem_Un_of_root_mem_adjoin | exact GlobalTheory.KZ.UnRoot.mem_Un_of_root_mem_adjoin | (intros; apply GlobalTheory.KZ.UnRoot.mem_Un_of_root_mem_adjoin <;> assumption)
