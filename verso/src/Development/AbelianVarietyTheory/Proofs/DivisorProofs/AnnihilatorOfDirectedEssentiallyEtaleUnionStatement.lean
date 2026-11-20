import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorOfDirectedEssentiallyEtaleUnion
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ann_of_directed_essEtale` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAnnihilatorOfDirectedEssentiallyEtaleUnion.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.annihilator_of_directed_essentiallyEtale_union : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] (C : ι → Subalgebra R B), Monotone C → (∀ b : B, ∃ i, b ∈ C i) → (∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime (Q.comap ((C i).val : C i →ₐ[R] B))))) → ∀ i, ∀ c ∈ C i, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C i, s ∉ Q ∧ s * c = 0 := by
  first | exact @GlobalTheory.ann_of_directed_essEtale | exact GlobalTheory.ann_of_directed_essEtale | (intros; apply GlobalTheory.ann_of_directed_essEtale <;> assumption)
