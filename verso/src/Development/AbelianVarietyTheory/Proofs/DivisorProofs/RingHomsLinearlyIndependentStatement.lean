import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsLinearlyIndependent
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ringHom_independent_via_algebraMap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRingHomsLinearlyIndependent.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.ring_homs_linearly_independent : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ], Function.Injective (algebraMap O C) → ∀ (S : Finset (Λ →+* O)) (c : (Λ →+* O) → C), (∀ a : Λ, ∑ σ ∈ S, c σ * algebraMap O C (σ a) = 0) → ∀ σ ∈ S, c σ = 0 := by
  first | exact @GlobalTheory.ringHom_independent_via_algebraMap | exact GlobalTheory.ringHom_independent_via_algebraMap | (intros; apply GlobalTheory.ringHom_independent_via_algebraMap <;> assumption)
