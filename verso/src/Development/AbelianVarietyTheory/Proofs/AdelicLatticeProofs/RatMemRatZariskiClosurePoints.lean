import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatPts

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
lemma _root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap {ι R : Type} [CommRing R] [Algebra ℚ R]
    (f : MvPolynomial (ι × ι) ℚ) (γ : Matrix ι ι ℚ) :
    _root_.GlobalTheory.ClassFin.ev f (γ.map (algebraMap ℚ R)) = algebraMap ℚ R (_root_.GlobalTheory.ClassFin.ev f γ) := by
  unfold _root_.GlobalTheory.ClassFin.ev
  rw [← MvPolynomial.aeval_algebraMap_apply]
  rfl

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.ClassFin.RatPts.rat_mem_pts : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ γ : Matrix ι ι ℚ, γ.map (algebraMap ℚ ℂ) ∈ Γ → γ ∈ _root_.GlobalTheory.ClassFin.pts Γ ℚ) ∧ ∀ (R : Type) [CommRing R] [Algebra ℚ R], ∀ γ ∈ _root_.GlobalTheory.ClassFin.pts Γ ℚ, γ.map (algebraMap ℚ R) ∈ _root_.GlobalTheory.ClassFin.pts Γ R := by
  intro ι _ _ Γ
  refine ⟨fun γ hγ => ?_, fun R _ _ γ hγ => ?_⟩
  · simp only [_root_.GlobalTheory.ClassFin.pts, Set.mem_setOf_eq]
    intro f hf
    have h := hf _ hγ
    rw [_root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap] at h
    exact (algebraMap ℚ ℂ).injective (by rw [h, map_zero])
  · simp only [_root_.GlobalTheory.ClassFin.pts, Set.mem_setOf_eq] at hγ ⊢
    intro f hf
    rw [_root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap, hγ f hf, map_zero]

end GlobalTheory.ClassFin.RatPts
