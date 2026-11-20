import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPerfectIdempotent
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDivGroup.exists_perfect_idempotent` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPerfectIdempotent.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_idempotent_nilpotent_complement_of_perfect : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), ∃ e : G ⟶ G, e ≫ e = e ∧ (∀ (n : ℕ) (a : G.A n), IsNilpotent (a - e.app n a)) ∧ ∀ (n : ℕ) (a : G.A n), IsNilpotent (e.app n a) → e.app n a = 0 := by
  first | exact @GlobalTheory.PDivGroup.exists_perfect_idempotent | exact GlobalTheory.PDivGroup.exists_perfect_idempotent | (intros; apply GlobalTheory.PDivGroup.exists_perfect_idempotent <;> assumption)
