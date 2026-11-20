import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCommutesHeckeAction
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.GamComm.act_galB_comm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGaloisCommutesHeckeAction.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.galois_commutes_hecke_action : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (N l w : ℕ) [Fact l.Prime], 1 ≤ N → ∀ b ∈ X.BSet N l w, ∀ δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l, ∀ s : Ω ≃ₐ[ℚ] Ω, X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) = X.galB l s (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  first | exact @GlobalTheory.KZ.GamComm.act_galB_comm | exact GlobalTheory.KZ.GamComm.act_galB_comm | (intros; apply GlobalTheory.KZ.GamComm.act_galB_comm <;> assumption)
