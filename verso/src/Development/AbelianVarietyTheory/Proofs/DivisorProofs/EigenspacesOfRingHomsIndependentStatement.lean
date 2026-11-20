import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenspacesOfRingHomsIndependent
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEigenspacesOfRingHomsIndependent.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.eigenspaces_of_ring_homs_independent : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), Function.Injective (algebraMap O C) → iSupIndep (fun σ : Λ →+* O => eig C (⇑ρ) σ) := by
  first | exact @GlobalTheory.iSupIndep_eig | exact GlobalTheory.iSupIndep_eig | (intros; apply GlobalTheory.iSupIndep_eig <;> assumption)
