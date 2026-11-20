import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCoprimeOfTorsion
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRelIndexCoprimeOfTorsion.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.relIndex_coprime_of_torsion : ∀ {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (l : ℕ), l.Prime → A ≤ B → B.FG →
    (∀ z ∈ B, ∃ n : ℕ, n.Coprime l ∧ n • z ∈ A) → A.relIndex B ≠ 0 ∧ (A.relIndex B).Coprime l := by
  first | exact @GlobalTheory.FGIndex.main | exact GlobalTheory.FGIndex.main | (intros; apply GlobalTheory.FGIndex.main <;> assumption)
