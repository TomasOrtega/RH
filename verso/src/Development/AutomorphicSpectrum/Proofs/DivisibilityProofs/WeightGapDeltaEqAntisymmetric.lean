import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

def xAt {Ψ : Type} {N : ℕ} (τ : Ψ) (i : ℕ) : MvPolynomial (Ψ × Fin N) ℝ :=
  if h : i < N then X (τ, ⟨i, h⟩) else 0

/- English proof (translation)
Simplify using `[xAt]`.
-/
theorem xAt_val {Ψ : Type} {N : ℕ} (τ : Ψ) (a : Fin N) :
    (xAt τ (a : ℕ) : MvPolynomial (Ψ × Fin N) ℝ) = X (τ, a) := by
  simp [xAt]

/- English proof (translation)
Simplify using `[PB.gapX, xAt]`.
-/
theorem gapX_eq_xAt_sub {Ψ : Type} {N : ℕ} (τ : Ψ) (s : Fin N) :
    PB.gapX (τ, s) = xAt τ (s : ℕ) - xAt τ ((s : ℕ) + 1) := by
  simp [PB.gapX, xAt]

/- English proof (translation)
Establish `h1 : ∑ s ∈ Finset.Ico a b, PB.gapX (τ, s) = ∑ i ∈ Finset.Ico (a : ℕ) (b : ℕ), ((xAt τ i : MvPolynomial (Ψ × Fin N) ℝ) - xAt τ (i + 1))`. Rewrite using `[← Fin.map_valEmbedding_Ico, Finset.sum_map]`. Conclude with `Finset.sum_congr rfl fun s _ => gapX_eq_xAt_sub τ s`. Establish `hle : (a : ℕ) ≤ b` using `hab`. Establish `h2 : ∀ n : ℕ, ∑ i ∈ Finset.Ico (a : ℕ) ((a : ℕ) + n), ((xAt τ i : MvPolynomial (Ψ × Fin N) ℝ) - xAt τ (i + 1)) = xAt τ (a : ℕ) - xAt τ ((a : ℕ) + n)`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[← add_assoc, Finset.sum_Ico_succ_top (Nat.le_add_right _ _), ih]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨n, hn⟩` from `Nat.exists_eq_add_of_le hle`. Rewrite using `[h1, hn, h2, ← hn, xAt_val, xAt_val]`.
-/
theorem sum_gapX_Ico {Ψ : Type} {N : ℕ} (τ : Ψ) {a b : Fin N} (hab : a ≤ b) :
    ∑ s ∈ Finset.Ico a b, PB.gapX (τ, s) = X (τ, a) - X (τ, b) := by
  have h1 : ∑ s ∈ Finset.Ico a b, PB.gapX (τ, s)
      = ∑ i ∈ Finset.Ico (a : ℕ) (b : ℕ),
          ((xAt τ i : MvPolynomial (Ψ × Fin N) ℝ) - xAt τ (i + 1)) := by
    rw [← Fin.map_valEmbedding_Ico, Finset.sum_map]
    exact Finset.sum_congr rfl fun s _ => gapX_eq_xAt_sub τ s
  have hle : (a : ℕ) ≤ b := hab
  have h2 : ∀ n : ℕ, ∑ i ∈ Finset.Ico (a : ℕ) ((a : ℕ) + n),
      ((xAt τ i : MvPolynomial (Ψ × Fin N) ℝ) - xAt τ (i + 1))
        = xAt τ (a : ℕ) - xAt τ ((a : ℕ) + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, Finset.sum_Ico_succ_top (Nat.le_add_right _ _), ih]
      ring
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hle
  rw [h1, hn, h2, ← hn, xAt_val, xAt_val]

/- English proof (translation)
Unfold `gapDelta GroundTheory.Heights₂.Heights.antisymDelta`. Simplify using `only [map_prod, map_sum]`. Use `Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b hb => ?_` and prove the remaining obligations. Establish `hab : a ≤ b` using `(Finset.mem_Ioi.1 hb).le`. Rewrite using `[← sum_gapX_Ico τ hab]`.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `[PB.toWt]`.
-/
theorem toWt_gapDelta_eq_antisymDelta (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    PB.toWt (gapDelta Ψ N) = GroundTheory.Heights₂.Heights.antisymDelta Ψ N := by
  unfold gapDelta GroundTheory.Heights₂.Heights.antisymDelta
  simp only [map_prod, map_sum]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun a _ =>
    Finset.prod_congr rfl fun b hb => ?_
  have hab : a ≤ b := (Finset.mem_Ioi.1 hb).le
  rw [← sum_gapX_Ico τ hab]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [PB.toWt]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
