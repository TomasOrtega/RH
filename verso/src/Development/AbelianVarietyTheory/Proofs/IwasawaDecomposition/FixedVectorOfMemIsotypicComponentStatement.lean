import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorOfMemIsotypicComponent
import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
open Formalism.L2 Formalism.AUTREP ReciprocityTheory.Aut NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFixedVectorOfMemIsotypicComponent.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.fixed_vector_of_mem_isotypic_component : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (K : Set (GAf L n)), NG.IsIrrRep ρ S → ∀ f ∈ NG.isoTyp ρ S, f ≠ 0 → (∀ κ ∈ K, NG.rt L n κ f = f) → ∃ f' ∈ S, f' ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ f' = f' := by
  first | exact @GlobalTheory.IsoFix.fixed_of_isoTyp | exact GlobalTheory.IsoFix.fixed_of_isoTyp | (intros; apply GlobalTheory.IsoFix.fixed_of_isoTyp <;> assumption)
