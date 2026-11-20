import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLowDegreeCoordsModMul
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_lowDegree_coords_mod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsLowDegreeCoordsModMul.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.exists_lowDegree_coords_mod_mul : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (g : A) (q : k[X]) (d : ℕ), g ≠ 0 → q ≠ 0 → (Algebra.norm k[X] g).natDegree + q.natDegree ≤ d + 1 →
 ∀ w : A, ∃ p : Fin n → k[X], (∀ i, (p i).natDegree ≤ d) ∧ w - ∑ i, p i • b i ∈ Ideal.span {g * algebraMap k[X] A q} := by
  first | exact @GlobalTheory.exists_lowDegree_coords_mod | exact GlobalTheory.exists_lowDegree_coords_mod | (intros; apply GlobalTheory.exists_lowDegree_coords_mod <;> assumption)
