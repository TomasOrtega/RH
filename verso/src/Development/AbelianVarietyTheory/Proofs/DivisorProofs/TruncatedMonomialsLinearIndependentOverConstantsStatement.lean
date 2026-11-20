import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedMonomialsLinearIndependentOverConstants
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTruncatedMonomialsLinearIndependentOverConstants.lean&line=101#L101)
-/
theorem _root_.GlobalTheory.T.truncatedMonomials_linearIndependent_over_constants : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] (d : ℕ) (x : Fin d → A) (E : Fin d → Derivation k A A), (∀ i j, E i (x j) = if i = j then 1 else 0) → ∀ B : Subalgebra k A, (∀ i, ∀ b ∈ B, E i b = 0) → LinearIndependent B (fun a : Fin d → Fin p => ∏ i, x i ^ (a i : ℕ)) := by
  first | exact @GlobalTheory.truncMono_linearIndependent | exact GlobalTheory.truncMono_linearIndependent | (intros; apply GlobalTheory.truncMono_linearIndependent <;> assumption)
