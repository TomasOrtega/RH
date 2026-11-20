import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormUnitLeOfEsymm

namespace GlobalTheory

open Polynomial in

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm`. Consider the case `exact _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm`. Consider the case `(apply _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm ..)`.
-/
theorem cauchy_roots_bound : ∀ (n : ℕ) (B : Multiset ℂˣ) (M : ℝ), B.card = n → 1 ≤ M →
    (∀ j, 1 ≤ j → j ≤ n → ‖(B.map fun b : ℂˣ => (b : ℂ)).esymm j‖ ≤ M) →
    ∀ b ∈ B, ‖(b : ℂ)‖ ≤ n * M := by
  first
  | exact @_root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm
  | exact _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm
  | (apply _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm <;> assumption)
  | (intros; apply _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm ..)

end GlobalTheory
