import Mathlib
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Complexify
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

/- English proof (translation)
Use `set D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := diagonal (fun i => ((d i : ℝ) : ℂ)) with hD`. Use `set B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) with hB`. Establish `h1 : g * D * g⁻¹ = X`. Rewrite using `[← hX, Matrix.mul_assoc, Matrix.mul_nonsing_inv g hg, Matrix.mul_one]`. Establish `h2 : trace (D * (g⁻¹ * B * g)) = trace (X * B)`.

Rewrite using `[← h1]`. Establish `: D * (g⁻¹ * B * g) = (D * g⁻¹ * B) * g`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[this, Matrix.trace_mul_comm]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[h2]`. Establish `h3 : trace (X * B) = ∑ u, ∑ w, X (e u) (e w) * (Matrix.fromBlocks Y 0 0 0 : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ) w u`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply]`. Rewrite using `[← Equiv.sum_comp e]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations.

Rewrite using `[← Equiv.sum_comp e]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `[hB, Matrix.reindex_apply]`. Rewrite using `[h3]`. Simplify using `only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, hb]`.

Simplify using `[Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]`.
-/
theorem trace_diagonal_block_conjugate (n : ℕ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hg : IsUnit g.det)
    (hX : X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)))
    (hb : ∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0)
    (Y : Matrix (Fin n) (Fin n) ℂ) :
    trace (diagonal (fun i => ((d i : ℝ) : ℂ)) * (g⁻¹ * Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) * g))
      = trace (diagonal (fun a => ((d' a : ℝ) : ℂ)) * Y) := by
  set D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := diagonal (fun i => ((d i : ℝ) : ℂ)) with hD
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) with hB
  have h1 : g * D * g⁻¹ = X := by
    rw [← hX, Matrix.mul_assoc, Matrix.mul_nonsing_inv g hg, Matrix.mul_one]
  have h2 : trace (D * (g⁻¹ * B * g)) = trace (X * B) := by
    rw [← h1]
    have : D * (g⁻¹ * B * g) = (D * g⁻¹ * B) * g := by
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [h2]
  have h3 : trace (X * B) = ∑ u, ∑ w, X (e u) (e w) *
      (Matrix.fromBlocks Y 0 0 0 : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ) w u := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [hB, Matrix.reindex_apply]
  rw [h3]
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero, hb]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]

end GlobalTheory.CompanionTheory.RgHeFrame
