import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyNilpotentAddScalar
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCharpolyNilpotentAddScalar.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.charpoly_nilpotent_add_scalar' : ∀ (k : Type) [Field k] (n : ℕ) (N : Matrix (Fin n) (Fin n) k) (c : k), IsNilpotent N → (N + Matrix.scalar (Fin n) c).charpoly = (X - C c) ^ n := by
  first | exact @GlobalTheory.charpoly_nilpotent_add_scalar | exact GlobalTheory.charpoly_nilpotent_add_scalar | (intros; apply GlobalTheory.charpoly_nilpotent_add_scalar <;> assumption)
