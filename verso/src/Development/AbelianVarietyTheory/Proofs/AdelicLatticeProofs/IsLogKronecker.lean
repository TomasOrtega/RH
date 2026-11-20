import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities.
-/
theorem isLog_kronecker {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} [Fintype κ] [DecidableEq κ]
    {H A : Matrix ι ι ℂ} {H' A' : Matrix κ κ ℂ} (h : IsLog H A) (h' : IsLog H' A') :
    IsLog (H ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ H') (A ⊗ₖ A') := by
  obtain ⟨U, d, hU, rfl, rfl⟩ := h
  obtain ⟨U', d', hU', rfl, rfl⟩ := h'
  refine ⟨U ⊗ₖ U', fun p => d p.1 + d' p.2, ?_, ?_, ?_⟩
  · rw [conjTranspose_kronecker, ← mul_kronecker_mul, hU, hU', one_kronecker_one]
  · have e : (diagonal (fun p : ι × κ => ((d p.1 + d' p.2 : ℝ) : ℂ))) =
        diagonal (fun i => (d i : ℂ)) ⊗ₖ (1 : Matrix κ κ ℂ) +
          (1 : Matrix ι ι ℂ) ⊗ₖ diagonal (fun i => (d' i : ℂ)) := by
      rw [← diagonal_one, ← diagonal_one, diagonal_kronecker_diagonal, diagonal_kronecker_diagonal,
        diagonal_add]
      congr 1
      funext p
      simp
    rw [e, conjTranspose_kronecker, Matrix.mul_add, Matrix.add_mul, ← mul_kronecker_mul,
      ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.mul_one,
      hU, hU']
  · have e : (diagonal (fun p : ι × κ => ((Real.exp (d p.1 + d' p.2) : ℝ) : ℂ))) =
        diagonal (fun i => (Real.exp (d i) : ℂ)) ⊗ₖ diagonal (fun i => (Real.exp (d' i) : ℂ)) := by
      rw [diagonal_kronecker_diagonal]
      congr 1
      funext p
      rw [Real.exp_add, Complex.ofReal_mul]
    rw [e, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. By extensionality, compare the relevant components.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem harm_kronecker : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ) (g' : σ → Matrix κ κ ℂ), Harm g → Harm g' → Harm (fun s => g s ⊗ₖ g' s) := by
  intro ι _ _ κ _ _ σ _ g g' ⟨H, hH, hs⟩ ⟨H', hH', hs'⟩
  refine ⟨fun s => H s ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ H' s, fun s => ?_, ?_⟩
  · have := isLog_kronecker (hH s) (hH' s)
    simpa only [conjTranspose_kronecker, ← mul_kronecker_mul] using this
  · ext ⟨i, k⟩ ⟨j, l⟩
    have h1 : ∑ s, H s i j = 0 := by
      have := congrFun (congrFun hs i) j
      simpa [Matrix.sum_apply] using this
    have h2 : ∑ s, H' s k l = 0 := by
      have := congrFun (congrFun hs' k) l
      simpa [Matrix.sum_apply] using this
    simp only [Matrix.sum_apply, Matrix.add_apply, kroneckerMap_apply, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, h1, h2, Matrix.zero_apply]
    simp

end GlobalTheory.ClassFin
